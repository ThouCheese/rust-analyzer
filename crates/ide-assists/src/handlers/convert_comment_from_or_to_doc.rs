use itertools::Itertools;
use syntax::{
    ast::{self, edit::IndentLevel, Comment, Whitespace},
    AstToken, Direction, SyntaxElement, TextRange,
};

use crate::{AssistContext, AssistId, AssistKind, Assists};

// Assist: comment_to_doc
//
// Converts comments to documentation.
//
// ```
//    // Wow what a nice function
//    // I sure hope this shows up when I hover over it
// ```
// ->
// ```
//    /// Wow what a nice function
//    /// I sure hope this shows up when I hover over it
// ```
pub(crate) fn convert_comment_from_or_to_doc(
    acc: &mut Assists,
    ctx: &AssistContext<'_>,
) -> Option<()> {
    let comment = ctx.find_token_at_offset::<ast::Comment>()?;

    match comment.kind().doc {
        Some(_) => doc_to_comment(acc, comment),
        None => {
            if let Some(doc_comment_style) = can_be_doc_comment(&comment) {
                comment_to_doc(acc, comment, doc_comment_style)
            } else {
                None
            }
        }
    }
}

fn doc_to_comment(acc: &mut Assists, comment: ast::Comment) -> Option<()> {
    let target = if comment.prefix() == "///" || comment.prefix() == "//!" {
        // Find all the comments we'll be collapsing into a block
        let comments = relevant_line_comments(&comment);
        let first_comment = &comments[0];
        let indentation = IndentLevel::from_token(first_comment.syntax());

        // Establish the target of our edit based on the comments we found
        TextRange::new(
            first_comment
                .syntax()
                .text_range()
                .start()
                .checked_sub((indentation.0 as u32 * 4).into())?,
            comments.last()?.syntax().text_range().end(),
        )
    } else {
        comment.syntax().text_range()
    };

    acc.add(
        AssistId("doc_to_comment", AssistKind::RefactorRewrite),
        "Replace a comment with doc comment",
        target,
        |edit| {
            // We need to either replace the first occurence of /* with /***, or we need to replace
            // the occurences // at the start of each line with ///
            let output = match comment.prefix() {
                line_start @ ("///" | "//!") => {
                    let indentation = IndentLevel::from_token(comment.syntax());
                    relevant_line_comments(&comment)
                        .iter()
                        .map(|comment| comment.text())
                        .flat_map(|text| text.lines())
                        .map(|line| indentation.to_string() + &line.replacen(line_start, "//", 1))
                        .join("\n")
                }
                block_start @ ("/**" | "/*!") => comment
                    .text()
                    .lines()
                    .enumerate()
                    .map(|(idx, line)| {
                        if idx == 0 {
                            line.replacen(block_start, "/*", 1)
                        } else {
                            line.replacen("*  ", "* ", 1)
                        }
                    })
                    .join("\n"),
                _ => panic!(),
            };
            edit.replace(target, output)
        },
    )
}

fn comment_to_doc(acc: &mut Assists, comment: ast::Comment, style: DocStyle) -> Option<()> {
    let target = if comment.prefix() == "//" {
        let comments = relevant_line_comments(&comment);
        let first_comment = &comments[0];
        let indentation = IndentLevel::from_token(first_comment.syntax());
        TextRange::new(
            first_comment
                .syntax()
                .text_range()
                .start()
                .checked_sub((indentation.0 as u32 * 4).into())?,
            comments.last()?.syntax().text_range().end(),
        )
    } else {
        comment.syntax().text_range()
    };

    acc.add(
        AssistId("comment_to_doc", AssistKind::RefactorRewrite),
        "Replace a doc comment with comment",
        target,
        |edit| {
            // We need to either replace the first occurence of /* with /***, or we need to replace
            // the occurences // at the start of each line with ///
            let output = match comment.prefix() {
                "//" => {
                    let line_start = match style {
                        DocStyle::Inner => "//!",
                        DocStyle::Outer => "///",
                    };
                    let indentation = IndentLevel::from_token(comment.syntax());
                    relevant_line_comments(&comment)
                        .iter()
                        .map(|comment| comment.text())
                        .flat_map(|text| text.lines())
                        .map(|line| indentation.to_string() + &line.replacen("//", line_start, 1))
                        .join("\n")
                }
                "/*" => {
                    let block_start = match style {
                        DocStyle::Inner => "/*!",
                        DocStyle::Outer => "/**",
                    };
                    comment
                        .text()
                        .lines()
                        .enumerate()
                        .map(|(idx, line)| {
                            if idx == 0 {
                                // On the first line we replace the comment start with a doc comment
                                // start.
                                line.replacen("/*", block_start, 1)
                            } else {
                                // put one extra space after each * since we moved the first line to
                                // the right by one column as well.
                                line.replacen("* ", "*  ", 1)
                            }
                        })
                        .join("\n")
                }
                _ => panic!(), // lmao
            };
            edit.replace(target, output)
        },
    )
}

enum DocStyle {
    /// //!
    Inner,
    /// ///
    Outer,
}

/// Not all comments are valid candidates for conversion into doc comments. For example, the
/// comments in the code:
/// ```rust
/// // foos the bar
/// fn foo_bar(foo: Foo) -> Bar {
///   // Bar the foo
///   foo.into_bar()
/// }
///
/// trait A {
///     // The A trait
/// }
/// ```
/// can be converted to doc comments. However, the comments in this example:
/// ```rust
/// fn foo_bar(foo: Foo /* not bar yet */) -> Bar {
///   foo.into_bar()
///   // Nicely done
/// }
/// // end of function
///
/// struct S {
///     // The S struct
/// }
/// ```
/// are not allowed to become doc comments.
fn can_be_doc_comment(comment: &ast::Comment) -> Option<DocStyle> {
    use syntax::SyntaxKind::*;

    // if the comment is not on its own line, then we do not propose anything.
    match comment.syntax().prev_token() {
        Some(prev) => {
            // There was a previous token, now check if it was a newline
            if Whitespace::cast(prev).filter(|w| w.text().contains('\n')).is_none() {
                // No newline found, this is a comment that is not on its own line and we don't
                // suggest anything.
                return None;
            }
        }
        // There is no previous token, this is the start of the file.
        None => return Some(DocStyle::Inner),
    }

    // check if comment is followed by: `struct`, `trait`, `mod`, `fn`, `type`, `extern crate`, `use`, `const`
    let parent_kind = comment.syntax().parent().map(|parent| parent.kind());
    if matches!(
        parent_kind,
        Some(STRUCT | TRAIT | MODULE | FN | TYPE_KW | EXTERN_CRATE | USE | CONST)
    ) {
        return Some(DocStyle::Outer);
    }

    // check if comment is preceded by: `fn f() {`, `trait T {`, `mod M {`
    let ppparent_kind = comment
        .syntax()
        .parent()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .map(|parent| parent.kind());

    if matches!(ppparent_kind, Some(FN | TRAIT | MODULE)) {
        return Some(DocStyle::Inner);
    }

    None

    // syntax allows doc comments on impl blocks, but it does nothing, so we don't propose it
}

/// The line -> block assist can  be invoked from anywhere within a sequence of line comments.
/// relevant_line_comments crawls backwards and forwards finding the complete sequence of comments that will
/// be joined.
pub(crate) fn relevant_line_comments(comment: &ast::Comment) -> Vec<Comment> {
    // The prefix identifies the kind of comment we're dealing with
    let prefix = comment.prefix();
    let same_prefix = |c: &ast::Comment| c.prefix() == prefix;

    // These tokens are allowed to exist between comments
    let skippable = |not: &SyntaxElement| {
        not.clone()
            .into_token()
            .and_then(Whitespace::cast)
            .map(|w| !w.spans_multiple_lines())
            .unwrap_or(false)
    };

    // Find all preceding comments (in reverse order) that have the same prefix
    let prev_comments = comment
        .syntax()
        .siblings_with_tokens(Direction::Prev)
        .filter(|s| !skippable(s))
        .map(|not| not.into_token().and_then(Comment::cast).filter(same_prefix))
        .take_while(|opt_com| opt_com.is_some())
        .flatten()
        .skip(1); // skip the first element so we don't duplicate it in next_comments

    let next_comments = comment
        .syntax()
        .siblings_with_tokens(Direction::Next)
        .filter(|s| !skippable(s))
        .map(|not| not.into_token().and_then(Comment::cast).filter(same_prefix))
        .take_while(|opt_com| opt_com.is_some())
        .flatten();

    let mut comments: Vec<_> = prev_comments.collect();
    comments.reverse();
    comments.extend(next_comments);
    comments
}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;
    // use crate::tests::check_assist_not_applicable;

    use super::*;

    #[test]
    fn module_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            // such a nice module$0
            fn main() {
                foo();
            }
            "#,
            r#"
            //! such a nice module
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_line_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            // unseen$0 docs
            fn main() {
                foo();
            }
            "#,
            r#"

            /// unseen docs
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_line_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            // unseen$0 docs
            // make me seen!
            fn main() {
                foo();
            }
            "#,
            r#"

            /// unseen docs
            /// make me seen!
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_line_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /// visible$0 docs
            fn main() {
                foo();
            }
            "#,
            r#"

            // visible docs
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_line_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /// visible$0 docs
            /// Hide me!
            fn main() {
                foo();
            }
            "#,
            r#"

            // visible docs
            // Hide me!
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_line_block_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /* unseen$0 docs */
            fn main() {
                foo();
            }
            "#,
            r#"

            /** unseen docs */
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_line_block_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /* unseen$0 docs
            *  make me seen!
            */
            fn main() {
                foo();
            }
            "#,
            r#"

            /** unseen docs
            *   make me seen!
            */
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_line_block_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /** visible$0 docs */
            fn main() {
                foo();
            }
            "#,
            r#"

            /* visible docs */
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_line_block_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"

            /** visible$0 docs
            *   Hide me!
            */
            fn main() {
                foo();
            }
            "#,
            r#"

            /* visible docs
            *  Hide me!
            */
            fn main() {
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_inner_line_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                // unseen$0 docs
                foo();
            }
            "#,
            r#"
            fn main() {
                //! unseen docs
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_inner_line_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                // unseen$0 docs
                // make me seen!
                foo();
            }
            "#,
            r#"
            fn main() {
                //! unseen docs
                //! make me seen!
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_inner_line_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                //! visible$0 docs
                foo();
            }
            "#,
            r#"
            fn main() {
                // visible docs
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_inner_line_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                //! visible$0 docs
                //! Hide me!
                foo();
            }
            "#,
            r#"
            fn main() {
                // visible docs
                // Hide me!
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_inner_line_block_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                /* unseen$0 docs */
                foo();
            }
            "#,
            r#"
            fn main() {
                /*! unseen docs */
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_inner_line_block_comment_to_doc() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                /* unseen$0 docs
                *  make me seen!
                */
                foo();
            }
            "#,
            r#"
            fn main() {
                /*! unseen docs
                *   make me seen!
                */
                foo();
            }
            "#,
        );
    }

    #[test]
    fn single_inner_line_block_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                /*! visible$0 docs */
                foo();
            }
            "#,
            r#"
            fn main() {
                /* visible docs */
                foo();
            }
            "#,
        );
    }

    #[test]
    fn multi_inner_line_block_doc_to_comment() {
        check_assist(
            convert_comment_from_or_to_doc,
            r#"
            fn main() {
                /*! visible$0 docs
                *   Hide me!
                */
                foo();
            }
            "#,
            r#"
            fn main() {
                /* visible docs
                *  Hide me!
                */
                foo();
            }
        "#,
        );
    }
}
