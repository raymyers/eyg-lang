use crate::token::Token;

pub fn lex(source: &str) -> Vec<(Token, usize)> {
    let bytes = source.as_bytes();
    let mut offset = 0;
    let mut tokens = Vec::new();

    while offset < bytes.len() {
        let start = offset;
        let (token, new_offset) = pop(bytes, offset);
        offset = new_offset;
        tokens.push((token, start));
    }

    tokens
}

fn pop(bytes: &[u8], start: usize) -> (Token, usize) {
    // Comment
    if bytes[start..].starts_with(b"//") {
        return scan_comment(bytes, start);
    }

    // Whitespace
    if matches!(bytes[start], b' ' | b'\t' | b'\n' | b'\r') {
        return scan_whitespace(bytes, start);
    }

    // Single-char structural tokens
    match bytes[start] {
        b'(' => return (Token::LeftParen, start + 1),
        b')' => return (Token::RightParen, start + 1),
        b'{' => return (Token::LeftBrace, start + 1),
        b'}' => return (Token::RightBrace, start + 1),
        b'[' => return (Token::LeftSquare, start + 1),
        b']' => return (Token::RightSquare, start + 1),
        b'=' => return (Token::Equal, start + 1),
        b',' => return (Token::Comma, start + 1),
        b':' => return (Token::Colon, start + 1),
        b'!' => return (Token::Bang, start + 1),
        b'|' => return (Token::Bar, start + 1),
        b'#' => return (Token::Hash, start + 1),
        b'@' => return (Token::At, start + 1),
        _ => {}
    }

    // Two-char tokens: -> and ..
    if bytes[start] == b'-' && start + 1 < bytes.len() && bytes[start + 1] == b'>' {
        return (Token::RightArrow, start + 2);
    }
    if bytes[start] == b'.' && start + 1 < bytes.len() && bytes[start + 1] == b'.' {
        return (Token::DotDot, start + 2);
    }

    // Single-char: dot (after .. check), minus (after -> check)
    if bytes[start] == b'.' {
        return (Token::Dot, start + 1);
    }
    if bytes[start] == b'-' {
        return (Token::Minus, start + 1);
    }

    // Keywords (greedy prefix match, before identifier check)
    if bytes[start..].starts_with(b"let") && !is_ident_continue(bytes, start + 3) {
        return (Token::Let, start + 3);
    }
    if bytes[start..].starts_with(b"match") && !is_ident_continue(bytes, start + 5) {
        return (Token::Match, start + 5);
    }
    if bytes[start..].starts_with(b"perform") && !is_ident_continue(bytes, start + 7) {
        return (Token::Perform, start + 7);
    }
    if bytes[start..].starts_with(b"deep") && !is_ident_continue(bytes, start + 4) {
        return (Token::Deep, start + 4);
    }
    if bytes[start..].starts_with(b"handle") && !is_ident_continue(bytes, start + 6) {
        return (Token::Handle, start + 6);
    }

    // String literals
    if bytes[start] == b'"' {
        return scan_string(bytes, start);
    }

    // Integer literals
    if bytes[start].is_ascii_digit() {
        return scan_integer(bytes, start);
    }

    // Lowercase identifiers (names)
    if bytes[start].is_ascii_lowercase() || bytes[start] == b'_' {
        return scan_name(bytes, start);
    }

    // Uppercase identifiers
    if bytes[start].is_ascii_uppercase() {
        return scan_uppername(bytes, start);
    }

    // Unexpected: consume entire remaining input (matches Gleam behavior)
    let raw = String::from_utf8_lossy(&bytes[start..]).into_owned();
    (Token::UnexpectedGrapheme(raw), bytes.len())
}

fn scan_comment(bytes: &[u8], start: usize) -> (Token, usize) {
    // Skip the "//"
    let mut pos = start + 2;
    let content_start = pos;
    while pos < bytes.len() && bytes[pos] != b'\n' && !(bytes[pos] == b'\r' && pos + 1 < bytes.len() && bytes[pos + 1] == b'\n') {
        pos += 1;
    }
    let content = String::from_utf8_lossy(&bytes[content_start..pos]).into_owned();
    (Token::Comment(content), pos)
}

fn scan_whitespace(bytes: &[u8], start: usize) -> (Token, usize) {
    let mut pos = start;
    while pos < bytes.len() {
        match bytes[pos] {
            b' ' | b'\t' | b'\n' => pos += 1,
            b'\r' if pos + 1 < bytes.len() && bytes[pos + 1] == b'\n' => pos += 2,
            _ => break,
        }
    }
    let raw = String::from_utf8_lossy(&bytes[start..pos]).into_owned();
    (Token::Whitespace(raw), pos)
}

fn scan_string(bytes: &[u8], start: usize) -> (Token, usize) {
    // Skip opening quote
    let mut pos = start + 1;
    let mut buffer = String::new();
    while pos < bytes.len() {
        match bytes[pos] {
            b'"' => {
                return (Token::String(buffer), pos + 1);
            }
            b'\\' => {
                pos += 1;
                if pos >= bytes.len() {
                    buffer.push('\\');
                    return (Token::UnterminatedString(buffer), pos);
                }
                match bytes[pos] {
                    b'"' => buffer.push('"'),
                    b'\\' => buffer.push('\\'),
                    b'n' => buffer.push('\n'),
                    b'r' => buffer.push('\r'),
                    b't' => buffer.push('\t'),
                    _ => panic!("invalid escape sequence"),
                }
                pos += 1;
            }
            ch => {
                buffer.push(ch as char);
                pos += 1;
            }
        }
    }
    (Token::UnterminatedString(buffer), pos)
}

fn scan_integer(bytes: &[u8], start: usize) -> (Token, usize) {
    let mut pos = start;
    while pos < bytes.len() && bytes[pos].is_ascii_digit() {
        pos += 1;
    }
    let raw = String::from_utf8_lossy(&bytes[start..pos]).into_owned();
    (Token::Integer(raw), pos)
}

fn scan_name(bytes: &[u8], start: usize) -> (Token, usize) {
    let mut pos = start;
    while pos < bytes.len()
        && (bytes[pos].is_ascii_lowercase()
            || bytes[pos].is_ascii_digit()
            || bytes[pos] == b'_')
    {
        pos += 1;
    }
    let raw = String::from_utf8_lossy(&bytes[start..pos]).into_owned();
    (Token::Name(raw), pos)
}

fn scan_uppername(bytes: &[u8], start: usize) -> (Token, usize) {
    let mut pos = start;
    while pos < bytes.len()
        && (bytes[pos].is_ascii_uppercase()
            || bytes[pos].is_ascii_lowercase()
            || bytes[pos].is_ascii_digit()
            || bytes[pos] == b'_')
    {
        pos += 1;
    }
    let raw = String::from_utf8_lossy(&bytes[start..pos]).into_owned();
    (Token::Uppername(raw), pos)
}

/// Check if the byte at the given offset is a valid identifier continuation character.
/// Returns false if offset is past end of input.
fn is_ident_continue(bytes: &[u8], offset: usize) -> bool {
    offset < bytes.len()
        && (bytes[offset].is_ascii_lowercase()
            || bytes[offset].is_ascii_uppercase()
            || bytes[offset].is_ascii_digit()
            || bytes[offset] == b'_')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok(tokens: &[(Token, usize)]) -> Vec<(&Token, usize)> {
        tokens.iter().map(|(t, o)| (t, *o)).collect()
    }

    #[test]
    fn test_empty() {
        assert_eq!(lex(""), vec![]);
    }

    #[test]
    fn test_grouping() {
        assert_eq!(
            lex("()"),
            vec![(Token::LeftParen, 0), (Token::RightParen, 1)]
        );
        assert_eq!(
            lex("{}"),
            vec![(Token::LeftBrace, 0), (Token::RightBrace, 1)]
        );
        assert_eq!(
            lex("[]"),
            vec![(Token::LeftSquare, 0), (Token::RightSquare, 1)]
        );
    }

    #[test]
    fn test_punctuation() {
        assert_eq!(
            lex("=->,.:!"),
            vec![
                (Token::Equal, 0),
                (Token::RightArrow, 1),
                (Token::Comma, 3),
                (Token::Dot, 4),
                (Token::Colon, 5),
                (Token::Bang, 6),
            ]
        );
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            lex("let match perform deep handle"),
            vec![
                (Token::Let, 0),
                (Token::Whitespace(" ".into()), 3),
                (Token::Match, 4),
                (Token::Whitespace(" ".into()), 9),
                (Token::Perform, 10),
                (Token::Whitespace(" ".into()), 17),
                (Token::Deep, 18),
                (Token::Whitespace(" ".into()), 22),
                (Token::Handle, 23),
            ]
        );
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            lex(r#""""hello""\\""#),
            vec![
                (Token::String("".into()), 0),
                (Token::String("hello".into()), 2),
                (Token::String("\\".into()), 9),
            ]
        );
    }

    #[test]
    fn test_numbers() {
        assert_eq!(
            lex("1 01 1000 -5"),
            vec![
                (Token::Integer("1".into()), 0),
                (Token::Whitespace(" ".into()), 1),
                (Token::Integer("01".into()), 2),
                (Token::Whitespace(" ".into()), 4),
                (Token::Integer("1000".into()), 5),
                (Token::Whitespace(" ".into()), 9),
                (Token::Minus, 10),
                (Token::Integer("5".into()), 11),
            ]
        );
    }

    #[test]
    fn test_names() {
        assert_eq!(
            lex("alice x1 _"),
            vec![
                (Token::Name("alice".into()), 0),
                (Token::Whitespace(" ".into()), 5),
                (Token::Name("x1".into()), 6),
                (Token::Whitespace(" ".into()), 8),
                (Token::Name("_".into()), 9),
            ]
        );
    }

    #[test]
    fn test_uppernames() {
        assert_eq!(
            lex("Ok MyThing A1"),
            vec![
                (Token::Uppername("Ok".into()), 0),
                (Token::Whitespace(" ".into()), 2),
                (Token::Uppername("MyThing".into()), 3),
                (Token::Whitespace(" ".into()), 10),
                (Token::Uppername("A1".into()), 11),
            ]
        );
    }

    #[test]
    fn test_call() {
        assert_eq!(
            lex("alice(1)"),
            vec![
                (Token::Name("alice".into()), 0),
                (Token::LeftParen, 5),
                (Token::Integer("1".into()), 6),
                (Token::RightParen, 7),
            ]
        );
        assert_eq!(
            lex("Ok(1)"),
            vec![
                (Token::Uppername("Ok".into()), 0),
                (Token::LeftParen, 2),
                (Token::Integer("1".into()), 3),
                (Token::RightParen, 4),
            ]
        );
    }

    #[test]
    fn test_unexpected_grapheme() {
        assert_eq!(lex("`"), vec![(Token::UnexpectedGrapheme("`".into()), 0)]);
    }

    #[test]
    fn test_unterminated_string() {
        assert_eq!(
            lex("\"ab"),
            vec![(Token::UnterminatedString("ab".into()), 0)]
        );
        assert_eq!(
            lex("\"xy\\"),
            vec![(Token::UnterminatedString("xy\\".into()), 0)]
        );
    }

    #[test]
    fn test_comment() {
        assert_eq!(
            lex("// hello\nx"),
            vec![
                (Token::Comment(" hello".into()), 0),
                (Token::Whitespace("\n".into()), 8),
                (Token::Name("x".into()), 9),
            ]
        );
    }

    #[test]
    fn test_keyword_not_prefix_of_name() {
        // "letter" should be Name, not Let + Name("ter")
        assert_eq!(lex("letter"), vec![(Token::Name("letter".into()), 0)]);
        assert_eq!(
            lex("matching"),
            vec![(Token::Name("matching".into()), 0)]
        );
        assert_eq!(
            lex("handle_it"),
            vec![(Token::Name("handle_it".into()), 0)]
        );
    }

    // Suppress unused function warning
    #[allow(dead_code)]
    fn _use_tok() {
        let tokens = lex("");
        let _ = tok(&tokens);
    }
}
