use lsp_types::{Position, Range};

#[must_use]
pub fn byte_offset_to_position(text: &str, byte_offset: usize) -> Position {
    let target = clamp_to_char_boundary(text, byte_offset.min(text.len()));
    let mut line: u32 = 0;
    let mut line_start = 0usize;

    for (idx, ch) in text.char_indices() {
        if idx >= target {
            break;
        }

        if ch == '\n' {
            line = line.saturating_add(1);
            line_start = idx + ch.len_utf8();
        }
    }

    let utf16_col = text[line_start..target]
        .chars()
        .map(char::len_utf16)
        .sum::<usize>();

    Position::new(line, u32::try_from(utf16_col).unwrap_or(u32::MAX))
}

#[must_use]
pub fn position_to_byte_offset(text: &str, position: Position) -> usize {
    let Some((line_start, line_end)) = line_bounds(text, position.line) else {
        return text.len();
    };

    let mut remaining_utf16 =
        usize::try_from(position.character).unwrap_or(usize::MAX);
    if remaining_utf16 == 0 {
        return line_start;
    }

    for (rel_idx, ch) in text[line_start..line_end].char_indices() {
        let utf16_width = ch.len_utf16();
        if remaining_utf16 < utf16_width {
            return line_start + rel_idx;
        }

        remaining_utf16 -= utf16_width;
        if remaining_utf16 == 0 {
            return line_start + rel_idx + ch.len_utf8();
        }
    }

    line_end
}

#[must_use]
pub fn byte_range_to_lsp_range(text: &str, start: usize, end: usize) -> Range {
    let clamped_start = start.min(text.len());
    let clamped_end = end.min(text.len());
    Range::new(
        byte_offset_to_position(text, clamped_start),
        byte_offset_to_position(text, clamped_end),
    )
}

#[must_use]
pub fn lsp_range_to_byte_range(text: &str, range: Range) -> (usize, usize) {
    (
        position_to_byte_offset(text, range.start),
        position_to_byte_offset(text, range.end),
    )
}

fn clamp_to_char_boundary(text: &str, mut offset: usize) -> usize {
    offset = offset.min(text.len());
    while offset > 0 && !text.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

fn line_bounds(text: &str, target_line: u32) -> Option<(usize, usize)> {
    if target_line == 0 {
        let end = text.find('\n').unwrap_or(text.len());
        return Some((0, end));
    }

    let mut current_line: u32 = 0;
    let mut line_start: Option<usize> = None;

    for (idx, ch) in text.char_indices() {
        if ch != '\n' {
            continue;
        }

        current_line = current_line.saturating_add(1);
        if current_line == target_line {
            line_start = Some(idx + ch.len_utf8());
            continue;
        }

        if current_line == target_line.saturating_add(1) {
            return line_start.map(|start| (start, idx));
        }
    }

    line_start.map(|start| (start, text.len()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_ascii_conversions() {
        let text = "hello\nworld";

        assert_eq!(byte_offset_to_position(text, 0), Position::new(0, 0));
        assert_eq!(byte_offset_to_position(text, 4), Position::new(0, 4));
        assert_eq!(byte_offset_to_position(text, 6), Position::new(1, 0));
        assert_eq!(position_to_byte_offset(text, Position::new(1, 3)), 9);
    }

    #[test]
    fn utf16_emoji_conversions_and_clamping() {
        let text = "a🦀b";

        assert_eq!(byte_offset_to_position(text, 1), Position::new(0, 1));
        assert_eq!(byte_offset_to_position(text, 5), Position::new(0, 3));
        assert_eq!(position_to_byte_offset(text, Position::new(0, 1)), 1);
        assert_eq!(position_to_byte_offset(text, Position::new(0, 3)), 5);
        assert_eq!(position_to_byte_offset(text, Position::new(0, 2)), 1);
    }

    #[test]
    fn utf16_multibyte_utf8_non_emoji_conversions() {
        let text = "日本語";

        assert_eq!(byte_offset_to_position(text, 0), Position::new(0, 0));
        assert_eq!(byte_offset_to_position(text, 3), Position::new(0, 1));
        assert_eq!(byte_offset_to_position(text, 6), Position::new(0, 2));
        assert_eq!(position_to_byte_offset(text, Position::new(0, 2)), 6);
    }

    #[test]
    fn utf16_offset_position_roundtrip_char_boundaries() {
        let text = "ab\n🦀z\n日本語";

        for offset in char_boundary_offsets(text) {
            let pos = byte_offset_to_position(text, offset);
            let actual = position_to_byte_offset(text, pos);
            assert_eq!(actual, offset, "failed roundtrip at offset {offset}");
        }
    }

    #[test]
    fn range_roundtrip_ascii() {
        let text = "hello\nworld";
        let source = (1usize, 8usize);

        let lsp = byte_range_to_lsp_range(text, source.0, source.1);
        let roundtrip = lsp_range_to_byte_range(text, lsp);

        assert_eq!(roundtrip, source);
    }

    #[test]
    fn range_roundtrip_with_emoji_and_multibyte() {
        let text = "a🦀b\n日本語";
        let source = (1usize, text.len());

        let lsp = byte_range_to_lsp_range(text, source.0, source.1);
        let roundtrip = lsp_range_to_byte_range(text, lsp);

        assert_eq!(roundtrip, source);
    }

    fn char_boundary_offsets(text: &str) -> Vec<usize> {
        text.char_indices()
            .map(|(idx, _)| idx)
            .chain(std::iter::once(text.len()))
            .collect()
    }
}
