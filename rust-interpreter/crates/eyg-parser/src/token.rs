use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Comment(String),
    Whitespace(String),
    Name(String),
    Uppername(String),
    Integer(String),
    String(String),
    Let,
    Match,
    Perform,
    Deep,
    Handle,
    Equal,
    Comma,
    DotDot,
    Dot,
    Colon,
    RightArrow,
    Minus,
    Bang,
    Bar,
    Hash,
    At,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftSquare,
    RightSquare,
    UnexpectedGrapheme(String),
    UnterminatedString(String),
}

pub fn drop_whitespace(tokens: Vec<(Token, usize)>) -> Vec<(Token, usize)> {
    tokens
        .into_iter()
        .filter(|(token, _)| !matches!(token, Token::Whitespace(_)))
        .collect()
}

pub fn drop_comments(tokens: Vec<(Token, usize)>) -> Vec<(Token, usize)> {
    tokens
        .into_iter()
        .filter(|(token, _)| !matches!(token, Token::Comment(_)))
        .collect()
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Comment(content) => write!(f, "//{content}"),
            Token::Whitespace(raw) => write!(f, "{raw}"),
            Token::Name(raw) => write!(f, "{raw}"),
            Token::Uppername(raw) => write!(f, "{raw}"),
            Token::Integer(raw) => write!(f, "{raw}"),
            Token::String(raw) => write!(f, "\"{raw}\""),
            Token::Let => write!(f, "let"),
            Token::Match => write!(f, "match"),
            Token::Perform => write!(f, "perform"),
            Token::Deep => write!(f, "deep"),
            Token::Handle => write!(f, "handle"),
            Token::Equal => write!(f, "="),
            Token::Comma => write!(f, ","),
            Token::DotDot => write!(f, ".."),
            Token::Dot => write!(f, "."),
            Token::Colon => write!(f, ":"),
            Token::RightArrow => write!(f, "->"),
            Token::Minus => write!(f, "-"),
            Token::Bang => write!(f, "!"),
            Token::Bar => write!(f, "|"),
            Token::Hash => write!(f, "#"),
            Token::At => write!(f, "@"),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::LeftBrace => write!(f, "{{"),
            Token::RightBrace => write!(f, "}}"),
            Token::LeftSquare => write!(f, "["),
            Token::RightSquare => write!(f, "]"),
            Token::UnexpectedGrapheme(raw) => write!(f, "{raw}"),
            Token::UnterminatedString(raw) => write!(f, "\"{raw}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_drop_whitespace() {
        let tokens = vec![
            (Token::Name("x".into()), 0),
            (Token::Whitespace(" ".into()), 1),
            (Token::Name("y".into()), 2),
            (Token::Whitespace("\n".into()), 3),
            (Token::Integer("42".into()), 4),
        ];
        let result = drop_whitespace(tokens);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0].0, Token::Name("x".into()));
        assert_eq!(result[1].0, Token::Name("y".into()));
        assert_eq!(result[2].0, Token::Integer("42".into()));
    }

    #[test]
    fn test_drop_comments() {
        let tokens = vec![
            (Token::Name("x".into()), 0),
            (Token::Comment(" a comment".into()), 1),
            (Token::Name("y".into()), 15),
        ];
        let result = drop_comments(tokens);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].0, Token::Name("x".into()));
        assert_eq!(result[1].0, Token::Name("y".into()));
    }

    #[test]
    fn test_display() {
        assert_eq!(Token::Let.to_string(), "let");
        assert_eq!(Token::RightArrow.to_string(), "->");
        assert_eq!(Token::Name("foo".into()).to_string(), "foo");
        assert_eq!(Token::String("hello".into()).to_string(), "\"hello\"");
        assert_eq!(Token::Integer("42".into()).to_string(), "42");
        assert_eq!(Token::Comment(" note".into()).to_string(), "// note");
    }
}
