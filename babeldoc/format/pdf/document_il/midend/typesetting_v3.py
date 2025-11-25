from __future__ import annotations

import copy
import logging
import re
import statistics
import unicodedata
from functools import cache

import pymupdf
import regex
from rtree import index

from babeldoc.const import WATERMARK_VERSION
from babeldoc.format.pdf.document_il import Box
from babeldoc.format.pdf.document_il import PdfCharacter
from babeldoc.format.pdf.document_il import PdfCurve
from babeldoc.format.pdf.document_il import PdfForm
from babeldoc.format.pdf.document_il import PdfFormula
from babeldoc.format.pdf.document_il import PdfParagraphComposition
from babeldoc.format.pdf.document_il import PdfStyle
from babeldoc.format.pdf.document_il import il_version_1
from babeldoc.format.pdf.document_il.utils.fontmap import FontMapper
from babeldoc.format.pdf.document_il.utils.formular_helper import update_formula_data
from babeldoc.format.pdf.document_il.utils.layout_helper import box_to_tuple
from babeldoc.format.pdf.translation_config import TranslationConfig
from babeldoc.format.pdf.translation_config import WatermarkOutputMode
from arabic_reshaper import reshape
from bidi.algorithm import get_display


logger = logging.getLogger(__name__)

LINE_BREAK_REGEX = regex.compile(
    r"^["
    r"a-z"
    r"A-Z"
    r"0-9"
    r"\u00C0-\u00FF"  # Latin-1 Supplement
    r"\u0100-\u017F"  # Latin Extended A
    r"\u0180-\u024F"  # Latin Extended B
    r"\u1E00-\u1EFF"  # Latin Extended Additional
    r"\u2C60-\u2C7F"  # Latin Extended C
    r"\uA720-\uA7FF"  # Latin Extended D
    r"\uAB30-\uAB6F"  # Latin Extended E
    r"\u0250-\u02A0"  # IPA Extensions
    r"\u0400-\u04FF"  # Cyrillic
    r"\u0300-\u036F"  # Combining Diacritical Marks
    r"\u0500-\u052F"  # Cyrillic Supplement
    r"\u0370-\u03FF"  # Greek and Coptic
    r"\u2DE0-\u2DFF"  # Cyrillic Extended-A
    r"\uA650-\uA69F"  # Cyrillic Extended-B
    r"\u1200-\u137F"  # Ethiopic
    r"\u1380-\u139F"  # Ethiopic Supplement
    r"\u2D80-\u2DDF"  # Ethiopic Extended
    r"\uAB00-\uAB2F"  # Ethiopic Extended-A
    r"\U0001E7E0-\U0001E7FF"  # Ethiopic Extended-B
    r"\u0E80-\u0EFF"  # Lao
    r"\u0D00-\u0D7F"  # Malayalam
    r"\u0A80-\u0AFF"  # Gujarati
    r"\u0E00-\u0E7F"  # Thai
    r"\u1000-\u109F"  # Myanmar
    r"\uAA60-\uAA7F"  # Myanmar Extended-A
    r"\uA9E0-\uA9FF"  # Myanmar Extended-B
    r"\U000116D0-\U000116FF"  # Myanmar Extended-C
    r"\u0B80-\u0BFF"  # Tamil
    r"\u0C00-\u0C7F"  # Telugu
    r"\u0B00-\u0B7F"  # Oriya
    r"\u0530-\u058F"  # Armenian
    r"\u10A0-\u10FF"  # Georgian
    r"\u1C90-\u1CBF"  # Georgian Extended
    r"\u2D00-\u2D2F"  # Georgian Supplement
    r"\u1780-\u17FF"  # Khmer
    r"\u19E0-\u19FF"  # Khmer Symbols
    r"\U00010B00-\U00010B3F"  # Avestan
    r"\u1D00-\u1D7F"  # Phonetic Extensions
    r"\u1400-\u167F"  # Unified Canadian Aboriginal Syllabics
    r"\u0B00-\u0B7F"  # Oriya
    r"\u0780-\u07BF"  # Thaana
    r"\U0001E900-\U0001E95F"  # Adlam
    r"\u1C80-\u1C8F"  # Cyrillic Extended-C
    r"\U0001E030-\U0001E08F"  # Cyrillic Extended-D
    r"\uA000-\uA48F"  # Yi Syllables
    r"\uA490-\uA4CF"  # Yi Radicals
    r"'"
    r"-"  # Hyphen
    r"Ã‚Â·"  # Middle Dot (U+00B7) For CatalÃƒÂ 
    r"ÃŠÂ»"  # Spacing Modifier Letters U+02BB
    r"]+$"
)


class TypesettingUnit:
    def __str__(self):
        return self.try_get_unicode() or ""

    def __init__(
        self,
        char: PdfCharacter | None = None,
        formular: PdfFormula | None = None,
        unicode: str | None = None,
        font: pymupdf.Font | None = None,
        original_font: il_version_1.PdfFont | None = None,
        font_size: float | None = None,
        style: PdfStyle | None = None,
        xobj_id: int | None = None,
        debug_info: bool = False,
    ):
        assert (char is not None) + (formular is not None) + (
            unicode is not None
        ) == 1, "Only one of chars and formular can be not None"
        self.char = char
        self.formular = formular
        self.unicode = unicode
        self.x = None
        self.y = None
        self.scale = None
        self.debug_info = debug_info

        # Cache variables
        self.box_cache: Box | None = None
        self.can_break_line_cache: bool | None = None
        self.is_cjk_char_cache: bool | None = None
        self.mixed_character_blacklist_cache: bool | None = None
        self.is_space_cache: bool | None = None
        self.is_hung_punctuation_cache: bool | None = None
        self.is_cannot_appear_in_line_end_punctuation_cache: bool | None = None
        self.can_passthrough_cache: bool | None = None
        self.width_cache: float | None = None
        self.height_cache: float | None = None

        self.font_size: float | None = None

        if unicode:
            assert font_size, "Font size must be provided when unicode is provided"
            assert style, "Style must be provided when unicode is provided"
            assert len(unicode) == 1, "Unicode must be a single character"
            assert xobj_id is not None, (
                "Xobj id must be provided when unicode is provided"
            )

            self.font = font
            if font is not None and hasattr(font, "font_id"):
                self.font_id = font.font_id
            else:
                self.font_id = "base"
            if original_font:
                self.original_font = original_font
            else:
                self.original_font = None

            self.font_size = font_size
            self.style = style
            self.xobj_id = xobj_id
    
    def try_resue_cache(self, old_tu: TypesettingUnit):
        if old_tu.is_cjk_char_cache is not None:
            self.is_cjk_char_cache = old_tu.is_cjk_char_cache

        if old_tu.can_break_line_cache is not None:
            self.can_break_line_cache = old_tu.can_break_line_cache

        if old_tu.is_space_cache is not None:
            self.is_space_cache = old_tu.is_space_cache

        if old_tu.is_hung_punctuation_cache is not None:
            self.is_hung_punctuation_cache = old_tu.is_hung_punctuation_cache

        if old_tu.is_cannot_appear_in_line_end_punctuation_cache is not None:
            self.is_cannot_appear_in_line_end_punctuation_cache = (
                old_tu.is_cannot_appear_in_line_end_punctuation_cache
            )

        if old_tu.can_passthrough_cache is not None:
            self.can_passthrough_cache = old_tu.can_passthrough_cache

        if old_tu.mixed_character_blacklist_cache is not None:
            self.mixed_character_blacklist_cache = (
                old_tu.mixed_character_blacklist_cache
            )


    def try_get_unicode(self) -> str | None:
        if self.char:
            return self.char.char_unicode
        elif self.formular:
            return None
        elif self.unicode:
            return self.unicode

    @property
    def mixed_character_blacklist(self):
        if self.mixed_character_blacklist_cache is None:
            self.mixed_character_blacklist_cache = self.calc_mixed_character_blacklist()

        return self.mixed_character_blacklist_cache

    def calc_mixed_character_blacklist(self):
        unicode = self.try_get_unicode()
        if unicode:
            return unicode in [
                "Ã£â‚¬â€š",
                "Ã¯Â¼Å’",
                "Ã¯Â¼Å¡",
                "Ã¯Â¼Å¸",
                "Ã¯Â¼Â",
            ]
        return False

    @property
    def can_break_line(self):
        if self.can_break_line_cache is None:
            self.can_break_line_cache = self.calc_can_break_line()

        return self.can_break_line_cache

    def calc_can_break_line(self):
        unicode = self.try_get_unicode()
        if not unicode:
            return True
        if LINE_BREAK_REGEX.match(unicode):
            return False
        return True

    @property
    def is_cjk_char(self):
        if self.is_cjk_char_cache is None:
            self.is_cjk_char_cache = self.calc_is_cjk_char()

        return self.is_cjk_char_cache

    def calc_is_cjk_char(self):
        if self.formular:
            return False
        unicode = self.try_get_unicode()
        if not unicode:
            return False
        if "(cid" in unicode:
            return False
        if len(unicode) > 1:
            return False
        assert len(unicode) == 1, "Unicode must be a single character"
        if unicode in [
            "Ã¯Â¼Ë†",
            "Ã¯Â¼â€°",
            "Ã£â‚¬Â",
            "Ã£â‚¬â€˜",
            "Ã£â‚¬Å ",
            "Ã£â‚¬â€¹",
            "Ã£â‚¬â€",
            "Ã£â‚¬â€¢",
            "Ã£â‚¬Ë†",
            "Ã£â‚¬â€°",
            "Ã£â‚¬â€“",
            "Ã£â‚¬â€”",
            "Ã£â‚¬Å’",
            "Ã£â‚¬Â",
            "Ã£â‚¬Å½",
            "Ã£â‚¬Â",
            "Ã£â‚¬Â",
            "Ã£â‚¬â€š",
            "Ã¯Â¼Å¡",
            "Ã¯Â¼Å¸",
            "Ã¯Â¼Â",
            "Ã¯Â¼Å’",
        ]:
            return True
        if unicode:
            if re.match(
                r"^["
                r"\u3000-\u303f"  # CJK Symbols and Punctuation
                r"\u3040-\u309f"  # Hiragana
                r"\u30a0-\u30ff"  # Katakana
                r"\u3100-\u312f"  # Bopomofo
                r"\uac00-\ud7af"  # Hangul Syllables
                r"\u1100-\u11ff"  # Hangul Jamo
                r"\u3130-\u318f"  # Hangul Compatibility Jamo
                r"\ua960-\ua97f"  # Hangul Jamo Extended-A
                r"\ud7b0-\ud7ff"  # Hangul Jamo Extended-B
                r"\u3190-\u319f"  # Kanbun
                r"\u3200-\u32ff"  # Enclosed CJK Letters and Months
                r"\u3300-\u33ff"  # CJK Compatibility
                r"\ufe30-\ufe4f"  # CJK Compatibility Forms
                r"\u4e00-\u9fff"  # CJK Unified Ideographs
                r"\u2e80-\u2eff"  # CJK Radicals Supplement
                r"\u31c0-\u31ef"  # CJK Strokes
                r"\u2f00-\u2fdf"  # Kangxi Radicals
                r"\ufe10-\ufe1f"  # Vertical Forms
                r"]+$",
                unicode,
            ):
                return True
            try:
                unicodedata_name = unicodedata.name(unicode)
                return (
                    "CJK UNIFIED IDEOGRAPH" in unicodedata_name
                    or "FULLWIDTH" in unicodedata_name
                )
            except ValueError:
                return False
        return False

    @property
    def is_space(self):
        if self.is_space_cache is None:
            self.is_space_cache = self.calc_is_space()

        return self.is_space_cache

    def calc_is_space(self):
        if self.formular:
            return False
        unicode = self.try_get_unicode()
        return unicode == " "

    @property
    def is_hung_punctuation(self):
        if self.is_hung_punctuation_cache is None:
            self.is_hung_punctuation_cache = self.calc_is_hung_punctuation()

        return self.is_hung_punctuation_cache

    def calc_is_hung_punctuation(self):
        if self.formular:
            return False
        unicode = self.try_get_unicode()

        if unicode:
            return unicode in [
                # Ã¨â€¹Â±Ã¦â€“â€¡Ã¦Â â€¡Ã§â€šÂ¹
                ",",
                ".",
                ":",
                ";",
                "?",
                "!",
                # Ã¤Â¸Â­Ã¦â€“â€¡Ã§â€šÂ¹Ã¥ÂÂ·
                "Ã¯Â¼Å’",  # Ã©â‚¬â€”Ã¥ÂÂ·
                "Ã£â‚¬â€š",  # Ã¥ÂÂ¥Ã¥ÂÂ·
                "Ã¯Â¼Å½",  # Ã¥â€¦Â¨Ã¨Â§â€™Ã¥ÂÂ¥Ã¥ÂÂ·
                "Ã£â‚¬Â",  # Ã©Â¡Â¿Ã¥ÂÂ·
                "Ã¯Â¼Å¡",  # Ã¥â€ â€™Ã¥ÂÂ·
                "Ã¯Â¼â€º",  # Ã¥Ë†â€ Ã¥ÂÂ·
                "Ã¯Â¼Â",  # Ã¥ÂÂ¹Ã¥ÂÂ·
                "Ã¢â‚¬Â¼",  # Ã¥ÂÅ’Ã¥ÂÂ¹Ã¥ÂÂ·
                "Ã¯Â¼Å¸",  # Ã©â€”Â®Ã¥ÂÂ·
                "Ã¢Ââ€¡",  # Ã¥ÂÅ’Ã©â€”Â®Ã¥ÂÂ·
                # Ã§Â»â€œÃ¦ÂÅ¸Ã¥Â¼â€¢Ã¥ÂÂ·
                "Ã¢â‚¬Â",  # Ã¥ÂÂ³Ã¥ÂÅ’Ã¥Â¼â€¢Ã¥ÂÂ·
                "Ã¢â‚¬â„¢",  # Ã¥ÂÂ³Ã¥Ââ€¢Ã¥Â¼â€¢Ã¥ÂÂ·
                "Ã£â‚¬Â",  # Ã¥ÂÂ³Ã§â€ºÂ´Ã¨Â§â€™Ã¥Ââ€¢Ã¥Â¼â€¢Ã¥ÂÂ·
                "Ã£â‚¬Â",  # Ã¥ÂÂ³Ã§â€ºÂ´Ã¨Â§â€™Ã¥ÂÅ’Ã¥Â¼â€¢Ã¥ÂÂ·
                # Ã§Â»â€œÃ¦ÂÅ¸Ã¦â€¹Â¬Ã¥ÂÂ·
                ")",  # Ã¥ÂÂ³Ã¥Å“â€ Ã¦â€¹Â¬Ã¥ÂÂ·
                "]",  # Ã¥ÂÂ³Ã¦â€“Â¹Ã¦â€¹Â¬Ã¥ÂÂ·
                "}",  # Ã¥ÂÂ³Ã¨Å Â±Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã¯Â¼â€°",  # Ã¥ÂÂ³Ã¥Å“â€ Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã£â‚¬â€¢",  # Ã¥ÂÂ³Ã©Â¾Å¸Ã§â€Â²Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã£â‚¬â€°",  # Ã¥ÂÂ³Ã¥Ââ€¢Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
                "Ã£â‚¬â€˜",  # Ã¥ÂÂ³Ã©Â»â€˜Ã¨â€°Â²Ã¦â€“Â¹Ã¥Â¤Â´Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã£â‚¬â€”",  # Ã¥ÂÂ³Ã§Â©ÂºÃ§â„¢Â½Ã¦â€“Â¹Ã¥Â¤Â´Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã¯Â¼Â½",  # Ã¥â€¦Â¨Ã¨Â§â€™Ã¥ÂÂ³Ã¦â€“Â¹Ã¦â€¹Â¬Ã¥ÂÂ·
                "Ã¯Â½Â",  # Ã¥â€¦Â¨Ã¨Â§â€™Ã¥ÂÂ³Ã¨Å Â±Ã¦â€¹Â¬Ã¥ÂÂ·
                # Ã§Â»â€œÃ¦ÂÅ¸Ã¥ÂÅ’Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
                "Ã£â‚¬â€¹",  # Ã¥ÂÂ³Ã¥ÂÅ’Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
                # Ã¨Â¿Å¾Ã¦Å½Â¥Ã¥ÂÂ·
                "Ã¯Â½Å¾",  # Ã¥â€¦Â¨Ã¨Â§â€™Ã¦Â³Â¢Ã¦ÂµÂªÃ¥ÂÂ·
                "-",  # Ã¨Â¿Å¾Ã¥Â­â€”Ã§Â¬Â¦Ã¥â€¡ÂÃ¥ÂÂ·
                "Ã¢â‚¬â€œ",  # Ã§Å¸Â­Ã§Â Â´Ã¦Å ËœÃ¥ÂÂ· (EN DASH)
                "Ã¢â‚¬â€",  # Ã©â€¢Â¿Ã§Â Â´Ã¦Å ËœÃ¥ÂÂ· (EM DASH)
                # Ã©â€”Â´Ã©Å¡â€Ã¥ÂÂ·
                "Ã‚Â·",  # Ã¤Â¸Â­Ã©â€”Â´Ã§â€šÂ¹
                "Ã£Æ’Â»",  # Ã§â€°â€¡Ã¥Ââ€¡Ã¥ÂÂÃ¤Â¸Â­Ã©â€”Â´Ã§â€šÂ¹
                "Ã¢â‚¬Â§",  # Ã¨Â¿Å¾Ã¥Â­â€”Ã§â€šÂ¹
                # Ã¥Ë†â€ Ã©Å¡â€Ã¥ÂÂ·
                "/",  # Ã¦â€“Å“Ã¦ÂÂ 
                "Ã¯Â¼Â",  # Ã¥â€¦Â¨Ã¨Â§â€™Ã¦â€“Å“Ã¦ÂÂ 
                "Ã¢Ââ€ž",  # Ã¥Ë†â€ Ã¦â€¢Â°Ã¦â€“Å“Ã¦ÂÂ 
            ]
        return False

    @property
    def is_cannot_appear_in_line_end_punctuation(self):
        if self.is_cannot_appear_in_line_end_punctuation_cache is None:
            self.is_cannot_appear_in_line_end_punctuation_cache = (
                self.calc_is_cannot_appear_in_line_end_punctuation()
            )

        return self.is_cannot_appear_in_line_end_punctuation_cache

    def calc_is_cannot_appear_in_line_end_punctuation(self):
        if self.formular:
            return False
        unicode = self.try_get_unicode()
        if not unicode:
            return False
        return unicode in [
            # Ã¥Â¼â‚¬Ã¥Â§â€¹Ã¥Â¼â€¢Ã¥ÂÂ·
            "Ã¢â‚¬Å“",  # Ã¥Â·Â¦Ã¥ÂÅ’Ã¥Â¼â€¢Ã¥ÂÂ·
            "Ã¢â‚¬Ëœ",  # Ã¥Â·Â¦Ã¥Ââ€¢Ã¥Â¼â€¢Ã¥ÂÂ·
            "Ã£â‚¬Å’",  # Ã¥Â·Â¦Ã§â€ºÂ´Ã¨Â§â€™Ã¥Ââ€¢Ã¥Â¼â€¢Ã¥ÂÂ·
            "Ã£â‚¬Å½",  # Ã¥Â·Â¦Ã§â€ºÂ´Ã¨Â§â€™Ã¥ÂÅ’Ã¥Â¼â€¢Ã¥ÂÂ·
            # Ã¥Â¼â‚¬Ã¥Â§â€¹Ã¦â€¹Â¬Ã¥ÂÂ·
            "(",  # Ã¥Â·Â¦Ã¥Å“â€ Ã¦â€¹Â¬Ã¥ÂÂ·
            "[",  # Ã¥Â·Â¦Ã¦â€“Â¹Ã¦â€¹Â¬Ã¥ÂÂ·
            "{",  # Ã¥Â·Â¦Ã¨Å Â±Ã¦â€¹Â¬Ã¥ÂÂ·
            "Ã¯Â¼Ë†",  # Ã¥Â·Â¦Ã¥Å“â€ Ã¦â€¹Â¬Ã¥ÂÂ·
            "Ã£â‚¬â€",  # Ã¥Â·Â¦Ã©Â¾Å¸Ã§â€Â²Ã¦â€¹Â¬Ã¥ÂÂ·
            "Ã£â‚¬Ë†",  # Ã¥Â·Â¦Ã¥Ââ€¢Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
            "Ã£â‚¬Å ",  # Ã¥Â·Â¦Ã¥ÂÅ’Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
            # Ã¥Â¼â‚¬Ã¥Â§â€¹Ã¥Ââ€¢Ã¥ÂÅ’Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
            "Ã£â‚¬â€“",  # Ã¥Â·Â¦Ã§Â©ÂºÃ§â„¢Â½Ã¦â€“Â¹Ã¥Â¤Â´Ã¦â€¹Â¬Ã¥ÂÂ·
            "Ã£â‚¬Ëœ",  # Ã¥Â·Â¦Ã©Â»â€˜Ã¨â€°Â²Ã¦â€“Â¹Ã¥Â¤Â´Ã¦â€¹Â¬Ã¥ÂÂ·
            "Ã£â‚¬Å¡",  # Ã¥Â·Â¦Ã¥Ââ€¢Ã¤Â¹Â¦Ã¥ÂÂÃ¥ÂÂ·
        ]

    def passthrough(
        self,
    ) -> tuple[list[PdfCharacter], list[PdfCurve], list[PdfForm]]:
        if self.char:
            return [self.char], [], []
        elif self.formular:
            return (
                self.formular.pdf_character,
                self.formular.pdf_curve,
                self.formular.pdf_form,
            )
        elif self.unicode:
            logger.error(f"Cannot passthrough unicode. TypesettingUnit: {self}. ")
            logger.error(f"Cannot passthrough unicode. TypesettingUnit: {self}. ")
            return [], [], []

    @property
    def can_passthrough(self):
        if self.can_passthrough_cache is None:
            self.can_passthrough_cache = self.calc_can_passthrough()

        return self.can_passthrough_cache

    def calc_can_passthrough(self):
        return self.unicode is None

    def calculate_box(self):
        if self.char:
            box = copy.deepcopy(self.char.box)
            if self.char.visual_bbox and self.char.visual_bbox.box:
                box.y = self.char.visual_bbox.box.y
                box.y2 = self.char.visual_bbox.box.y2
                # return self.char.visual_bbox.box

            return box
        elif self.formular:
            return self.formular.box
            # if self.formular.x_offset <= 0.5:
            #     return self.formular.box
            # formular_box = copy.copy(self.formular.box)
            # formular_box.x2 += self.formular.x_advance
            # return formular_box
        elif self.unicode:
            char_width = self.font.char_lengths(self.unicode, self.font_size)[0]
            if self.x is None or self.y is None or self.scale is None:
                return Box(0, 0, char_width, self.font_size)
            return Box(self.x, self.y, self.x + char_width, self.y + self.font_size)

    @property
    def box(self):
        if not self.box_cache:
            self.box_cache = self.calculate_box()

        return self.box_cache

    @property
    def width(self):
        if self.width_cache is None:
            self.width_cache = self.calc_width()

        return self.width_cache

    def calc_width(self):
        box = self.box
        return box.x2 - box.x

    @property
    def height(self):
        if self.height_cache is None:
            self.height_cache = self.calc_height()

        return self.height_cache

    def calc_height(self):
        box = self.box
        return box.y2 - box.y

    def relocate(
        self,
        x: float,
        y: float,
        scale: float,
    ) -> TypesettingUnit:
        """Ã©â€¡ÂÃ¥Â®Å¡Ã¤Â½ÂÃ¥Â¹Â¶Ã§Â¼Â©Ã¦â€Â¾Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’

        Args:
            x: Ã¦â€“Â°Ã§Å¡â€ž x Ã¥ÂÂÃ¦Â â€¡
            y: Ã¦â€“Â°Ã§Å¡â€ž y Ã¥ÂÂÃ¦Â â€¡
            scale: Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â

        Returns:
            Ã¦â€“Â°Ã§Å¡â€žÃ¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’
        """
        if self.char:
            # Ã¥Ë†â€ºÃ¥Â»ÂºÃ¦â€“Â°Ã§Å¡â€žÃ¥Â­â€”Ã§Â¬Â¦Ã¥Â¯Â¹Ã¨Â±Â¡
            new_char = PdfCharacter(
                pdf_character_id=self.char.pdf_character_id,
                char_unicode=self.char.char_unicode,
                box=Box(
                    x=x,
                    y=y,
                    x2=x + self.width * scale,
                    y2=y + self.height * scale,
                ),
                pdf_style=PdfStyle(
                    font_id=self.char.pdf_style.font_id,
                    font_size=self.char.pdf_style.font_size * scale,
                    graphic_state=self.char.pdf_style.graphic_state,
                ),
                scale=scale,
                vertical=self.char.vertical,
                advance=self.char.advance * scale if self.char.advance else None,
                debug_info=self.debug_info,
                xobj_id=self.char.xobj_id,
            )
            new_tu = TypesettingUnit(char=new_char)
            new_tu.try_resue_cache(self)
            return new_tu

        elif self.formular:
            # Ã¥Ë†â€ºÃ¥Â»ÂºÃ¦â€“Â°Ã§Å¡â€žÃ¥â€¦Â¬Ã¥Â¼ÂÃ¥Â¯Â¹Ã¨Â±Â¡Ã¯Â¼Å’Ã¤Â¿ÂÃ¦Å’ÂÃ¥â€ â€¦Ã©Æ’Â¨Ã¥Â­â€”Ã§Â¬Â¦Ã§Å¡â€žÃ§â€ºÂ¸Ã¥Â¯Â¹Ã¤Â½ÂÃ§Â½Â®
            new_chars = []
            min_x = self.formular.box.x
            min_y = self.formular.box.y

            for char in self.formular.pdf_character:
                # Ã¨Â®Â¡Ã§Â®â€”Ã§â€ºÂ¸Ã¥Â¯Â¹Ã¤Â½ÂÃ§Â½Â®
                rel_x = char.box.x - min_x
                rel_y = char.box.y - min_y

                visual_rel_x = char.visual_bbox.box.x - min_x
                visual_rel_y = char.visual_bbox.box.y - min_y

                # Ã¥Ë†â€ºÃ¥Â»ÂºÃ¦â€“Â°Ã§Å¡â€žÃ¥Â­â€”Ã§Â¬Â¦Ã¥Â¯Â¹Ã¨Â±Â¡
                new_char = PdfCharacter(
                    pdf_character_id=char.pdf_character_id,
                    char_unicode=char.char_unicode,
                    box=Box(
                        x=x + (rel_x + self.formular.x_offset) * scale,
                        y=y + (rel_y + self.formular.y_offset) * scale,
                        x2=x
                        + (rel_x + (char.box.x2 - char.box.x) + self.formular.x_offset)
                        * scale,
                        y2=y
                        + (rel_y + (char.box.y2 - char.box.y) + self.formular.y_offset)
                        * scale,
                    ),
                    visual_bbox=il_version_1.VisualBbox(
                        box=Box(
                            x=x + (visual_rel_x + self.formular.x_offset) * scale,
                            y=y + (visual_rel_y + self.formular.y_offset) * scale,
                            x2=x
                            + (
                                visual_rel_x
                                + (char.visual_bbox.box.x2 - char.visual_bbox.box.x)
                                + self.formular.x_offset
                            )
                            * scale,
                            y2=y
                            + (
                                visual_rel_y
                                + (char.visual_bbox.box.y2 - char.visual_bbox.box.y)
                                + self.formular.y_offset
                            )
                            * scale,
                        ),
                    ),
                    pdf_style=PdfStyle(
                        font_id=char.pdf_style.font_id,
                        font_size=char.pdf_style.font_size * scale,
                        graphic_state=char.pdf_style.graphic_state,
                    ),
                    scale=scale,
                    vertical=char.vertical,
                    advance=char.advance * scale if char.advance else None,
                    xobj_id=char.xobj_id,
                )
                new_chars.append(new_char)

            # Calculate bounding box from new_chars
            min_x = min(char.visual_bbox.box.x for char in new_chars)
            min_y = min(char.visual_bbox.box.y for char in new_chars)
            max_x = max(char.visual_bbox.box.x2 for char in new_chars)
            max_y = max(char.visual_bbox.box.y2 for char in new_chars)

            new_formula = PdfFormula(
                box=Box(
                    x=min_x,
                    y=min_y,
                    x2=max_x,
                    y2=max_y,
                ),
                pdf_character=new_chars,
                x_offset=self.formular.x_offset * scale,
                y_offset=self.formular.y_offset * scale,
                x_advance=self.formular.x_advance * scale,
            )

            # Handle contained curves
            new_curves = []
            for curve in self.formular.pdf_curve:
                new_curve = self._transform_curve_for_relocation(
                    curve,
                    self.formular.box.x,
                    self.formular.box.y,
                    x,
                    y,
                    scale,
                )
                new_curves.append(new_curve)
            new_formula.pdf_curve = new_curves

            # Handle contained forms
            new_forms = []
            for form in self.formular.pdf_form:
                new_form = self._transform_form_for_relocation(
                    form, self.formular.box.x, self.formular.box.y, x, y, scale
                )
                new_forms.append(new_form)
            new_formula.pdf_form = new_forms

            update_formula_data(new_formula)

            new_tu = TypesettingUnit(formular=new_formula)
            new_tu.try_resue_cache(self)
            return new_tu

        elif self.unicode:
            # Ã¥Â¯Â¹Ã¤ÂºÅ½ Unicode Ã¥Â­â€”Ã§Â¬Â¦Ã¯Â¼Å’Ã¦Ë†â€˜Ã¤Â»Â¬Ã¥Â­ËœÃ¥â€šÂ¨Ã¦â€“Â°Ã§Å¡â€žÃ¤Â½ÂÃ§Â½Â®Ã¤Â¿Â¡Ã¦ÂÂ¯
            new_unit = TypesettingUnit(
                unicode=self.unicode,
                font=self.font,
                original_font=self.original_font,
                font_size=self.font_size * scale,
                style=self.style,
                xobj_id=self.xobj_id,
                debug_info=self.debug_info,
            )
            new_unit.x = x
            new_unit.y = y
            new_unit.scale = scale
            new_unit.try_resue_cache(self)
            return new_unit

    def _transform_curve_for_relocation(
        self,
        curve,
        original_formula_x: float,
        original_formula_y: float,
        new_x: float,
        new_y: float,
        scale: float,
    ):
        """Transform a curve for formula relocation."""
        import copy

        new_curve = copy.deepcopy(curve)

        if new_curve.box:
            # Calculate relative position to formula's original position (same as chars)
            rel_x = new_curve.box.x - original_formula_x
            rel_y = new_curve.box.y - original_formula_y

            # Apply same transformation as characters
            new_curve.box = Box(
                x=new_x + (rel_x + self.formular.x_offset) * scale,
                y=new_y + (rel_y + self.formular.y_offset) * scale,
                x2=new_x
                + (
                    rel_x
                    + (new_curve.box.x2 - new_curve.box.x)
                    + self.formular.x_offset
                )
                * scale,
                y2=new_y
                + (
                    rel_y
                    + (new_curve.box.y2 - new_curve.box.y)
                    + self.formular.y_offset
                )
                * scale,
            )

        # Set relocation transform instead of modifying original CTM
        translation_x = (
            new_x + self.formular.x_offset * scale - original_formula_x * scale
        )
        translation_y = (
            new_y + self.formular.y_offset * scale - original_formula_y * scale
        )

        # Create relocation transformation matrix
        from babeldoc.format.pdf.document_il.utils.matrix_helper import (
            create_translation_and_scale_matrix,
        )

        relocation_matrix = create_translation_and_scale_matrix(
            translation_x, translation_y, scale
        )
        new_curve.relocation_transform = list(relocation_matrix)

        return new_curve

    def _transform_form_for_relocation(
        self,
        form,
        original_formula_x: float,
        original_formula_y: float,
        new_x: float,
        new_y: float,
        scale: float,
    ):
        """Transform a form for formula relocation."""
        import copy

        new_form = copy.deepcopy(form)

        if new_form.box:
            # Calculate relative position to formula's original position (same as chars)
            rel_x = new_form.box.x - original_formula_x
            rel_y = new_form.box.y - original_formula_y

            # Apply same transformation as characters
            new_form.box = Box(
                x=new_x + (rel_x + self.formular.x_offset) * scale,
                y=new_y + (rel_y + self.formular.y_offset) * scale,
                x2=new_x
                + (rel_x + (new_form.box.x2 - new_form.box.x) + self.formular.x_offset)
                * scale,
                y2=new_y
                + (rel_y + (new_form.box.y2 - new_form.box.y) + self.formular.y_offset)
                * scale,
            )

        # Set relocation transform instead of modifying original matrices
        translation_x = (
            new_x + self.formular.x_offset * scale - original_formula_x * scale
        )
        translation_y = (
            new_y + self.formular.y_offset * scale - original_formula_y * scale
        )

        # Create relocation transformation matrix
        from babeldoc.format.pdf.document_il.utils.matrix_helper import (
            create_translation_and_scale_matrix,
        )

        relocation_matrix = create_translation_and_scale_matrix(
            translation_x, translation_y, scale
        )
        new_form.relocation_transform = list(relocation_matrix)

        return new_form

    def render(
        self,
    ) -> tuple[list[PdfCharacter], list[PdfCurve], list[PdfForm]]:
        """Ã¦Â¸Â²Ã¦Å¸â€œÃ¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¤Â¸Âº PdfCharacter Ã¥Ë†â€”Ã¨Â¡Â¨

        Returns:
            PdfCharacter Ã¥Ë†â€”Ã¨Â¡Â¨
        """
        if self.can_passthrough:
            return self.passthrough()
        elif self.unicode:
            assert self.x is not None, (
                "x position must be set, should be set by `relocate`"
            )
            assert self.y is not None, (
                "y position must be set, should be set by `relocate`"
            )
            assert self.scale is not None, (
                "scale must be set, should be set by `relocate`"
            )
            x = self.x
            y = self.y
            # if self.original_font and self.font and hasattr(self.original_font, "descent") and hasattr(self.font, "descent_fontmap"):
            #     original_descent = self.original_font.descent
            #     new_descent = self.font.descent_fontmap
            #     y -= (original_descent - new_descent) * self.font_size / 1000

            # Ã¨Â®Â¡Ã§Â®â€”Ã¥Â­â€”Ã§Â¬Â¦Ã¥Â®Â½Ã¥ÂºÂ¦
            char_width = self.width

            # Handle case when font is None (no suitable font found for this character)
            if self.font is None:
                logger.warning(
                    f"No font available for character '{self.unicode}' (U+{ord(self.unicode):04X}), "
                    f"using font_id='{self.font_id}' with glyph_id=0"
                )
                glyph_id = 0  # Use glyph 0 as fallback (usually .notdef)
            else:
                glyph_id = self.font.has_glyph(ord(self.unicode))
                if glyph_id == 0 or glyph_id is None:
                    logger.warning(
                        f"Font '{self.font_id}' doesn't have glyph for character '{self.unicode}' (U+{ord(self.unicode):04X}), "
                        f"using glyph_id=0"
                    )
                    glyph_id = 0

            new_char = PdfCharacter(
                pdf_character_id=glyph_id,
                char_unicode=self.unicode,
                box=Box(
                    x=x,  # Ã¤Â½Â¿Ã§â€Â¨Ã¥Â­ËœÃ¥â€šÂ¨Ã§Å¡â€žÃ¤Â½ÂÃ§Â½Â®
                    y=y,
                    x2=x + char_width,
                    y2=y + self.font_size,
                ),
                pdf_style=PdfStyle(
                    font_id=self.font_id,
                    font_size=self.font_size,
                    graphic_state=self.style.graphic_state,
                ),
                scale=self.scale,
                vertical=False,
                advance=char_width,
                xobj_id=self.xobj_id,
                debug_info=self.debug_info,
            )
            return [new_char], [], []
        else:
            logger.error(f"Unknown typesetting unit. TypesettingUnit: {self}. ")
            logger.error(f"Unknown typesetting unit. TypesettingUnit: {self}. ")
            return [], [], []


class Typesetting:
    stage_name = "Typesetting"

    def __init__(self, translation_config: TranslationConfig):
        self.font_mapper = FontMapper(translation_config)
        self.translation_config = translation_config
        self.lang_code = self.translation_config.lang_out.upper()
        # Ensure detailed_logger attribute exists to avoid attribute access errors
        self.detailed_logger = None
        self.is_cjk = (
            # Why zh-CN/zh-HK/zh-TW here but not zh-Hans and so on?
            # See https://funstory-ai.github.io/BabelDOC/supported_languages/
            ("ZH" in self.lang_code)  # C
            or ("JA" in self.lang_code)
            or ("JP" in self.lang_code)  # J
            or ("KR" in self.lang_code)  # K
            or ("CN" in self.lang_code)
            or ("HK" in self.lang_code)
            or ("TW" in self.lang_code)
        )

    def preprocess_document(self, document: il_version_1.Document, pbar):
        """Ã©Â¢â€žÃ¥Â¤â€žÃ§Ââ€ Ã¦â€“â€¡Ã¦Â¡Â£Ã¯Â¼Å’Ã¨Å½Â·Ã¥Ââ€“Ã¦Â¯ÂÃ¤Â¸ÂªÃ¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¦Å“â‚¬Ã¤Â¼ËœÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¯Â¼Å’Ã¤Â¸ÂÃ¦â€°Â§Ã¨Â¡Å’Ã¥Â®Å¾Ã©â„¢â€¦Ã¦Å½â€™Ã§â€°Ë†"""
        all_scales: list[float] = []
        all_paragraphs: list[il_version_1.PdfParagraph] = []

        for page in document.page:
            pbar.advance()
            # Ã¥â€¡â€ Ã¥Â¤â€¡Ã¥Â­â€”Ã¤Â½â€œÃ¤Â¿Â¡Ã¦ÂÂ¯Ã¯Â¼Ë†Ã¥Â¤ÂÃ¥Ë†Â¶Ã¨â€¡Âª render_page Ã§Å¡â€žÃ©â‚¬Â»Ã¨Â¾â€˜Ã¯Â¼â€°
            fonts: dict[
                str | int,
                il_version_1.PdfFont | dict[str, il_version_1.PdfFont],
            ] = {f.font_id: f for f in page.pdf_font if f.font_id}
            page_fonts = {f.font_id: f for f in page.pdf_font if f.font_id}
            for k, v in self.font_mapper.fontid2font.items():
                fonts[k] = v
            for xobj in page.pdf_xobject:
                if xobj.xobj_id is not None:
                    fonts[xobj.xobj_id] = page_fonts.copy()
                    for font in xobj.pdf_font:
                        if (
                            xobj.xobj_id in fonts
                            and isinstance(fonts[xobj.xobj_id], dict)
                            and font.font_id
                        ):
                            fonts[xobj.xobj_id][font.font_id] = font

            # Ã¥Â¤â€žÃ§Ââ€ Ã¦Â¯ÂÃ¤Â¸ÂªÃ¦Â®ÂµÃ¨ÂÂ½
            for paragraph in page.pdf_paragraph:
                all_paragraphs.append(paragraph)
                unit_count = 0
                try:
                    typesetting_units = self.create_typesetting_units(paragraph, fonts)
                    unit_count = len(typesetting_units)
                    for unit in typesetting_units:
                        if unit.formular:
                            unit_count += len(unit.formular.pdf_character) - 1

                    # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦â€°â‚¬Ã¦Å“â€°Ã¥Ââ€¢Ã¥â€¦Æ’Ã©Æ’Â½Ã¥ÂÂ¯Ã¤Â»Â¥Ã§â€ºÂ´Ã¦Å½Â¥Ã¤Â¼Â Ã©â‚¬â€™Ã¯Â¼Å’Ã¥Ë†â„¢ scale = 1.0
                    if all(unit.can_passthrough for unit in typesetting_units):
                        paragraph.optimal_scale = 1.0
                    else:
                        # Ã¨Å½Â·Ã¥Ââ€“Ã¦Å“â‚¬Ã¤Â¼ËœÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
                        optimal_scale = self._get_optimal_scale(
                            paragraph, page, typesetting_units
                        )
                        paragraph.optimal_scale = optimal_scale
                except Exception as e:
                    # Ã¥Â¦â€šÃ¦Å¾Å“Ã©Â¢â€žÃ¥Â¤â€žÃ§Ââ€ Ã¥â€¡ÂºÃ©â€â„¢Ã¯Â¼Å’Ã©Â»ËœÃ¨Â®Â¤Ã¤Â½Â¿Ã§â€Â¨ 1.0 Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
                    logger.warning(f"Ã©Â¢â€žÃ¥Â¤â€žÃ§Ââ€ Ã¦Â®ÂµÃ¨ÂÂ½Ã¦â€”Â¶Ã¥â€¡ÂºÃ©â€â„¢Ã¯Â¼Å¡{e}")
                    paragraph.optimal_scale = 1.0

                if paragraph.optimal_scale is not None:
                    all_scales.extend([paragraph.optimal_scale] * unit_count)

        # Ã¨Å½Â·Ã¥Ââ€“Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ§Å¡â€žÃ¤Â¼â€”Ã¦â€¢Â°
        if all_scales:
            try:
                modes = statistics.multimode(all_scales)
                mode_scale = min(modes)
            except statistics.StatisticsError:
                logger.warning(
                    "Could not find a mode for paragraph scales. Falling back to median."
                )
                mode_scale = statistics.median(all_scales)
            # Ã¥Â°â€ Ã¦â€°â‚¬Ã¦Å“â€°Ã¥Â¤Â§Ã¤ÂºÅ½Ã¤Â¼â€”Ã¦â€¢Â°Ã§Å¡â€žÃ¥â‚¬Â¼Ã¤Â¿Â®Ã¦â€Â¹Ã¤Â¸ÂºÃ¤Â¼â€”Ã¦â€¢Â°
            for paragraph in all_paragraphs:
                if (
                    paragraph.optimal_scale is not None
                    and paragraph.optimal_scale > mode_scale
                ):
                    paragraph.optimal_scale = mode_scale
        else:
            logger.error(
                "document_scales is empty, there seems no paragraph in this PDF"
            )

    def shape_arabic_text(self, text: str) -> str:
        """Shape and reorder Arabic text if output language is Arabic.

        Args:
            text: Input text to shape

        Returns:
            Shaped and reordered text if language is Arabic, original text otherwise
        """
        if not text:
            return text

        # Robust Arabic output detection: accept explicit 'ar', 'ara', 'arabic'
        # or formats containing '-ar', '->ar', or '/ar' as a target marker (e.g. 'en-ar', 'en->ar')
        lang_out = (self.translation_config.lang_out or "").lower()
        is_arabic = False
        if lang_out in ("en-ar, ar", "ara", "arabic"):
            is_arabic = True
        elif "-ar" in lang_out or "->ar" in lang_out or "/ar" in lang_out:
            is_arabic = True

        if is_arabic:
            logger.debug("Shaping Arabic text")
            # Flip parentheses and brackets for RTL display
            # text = text.replace("(", "\x00")
            # text = text.replace(")", "(")
            # text = text.replace("\x00", ")")
            # text = text.replace("[", "\x01")
            # text = text.replace("]", "[")
            # text = text.replace("\x01", "]")
            # text = text.replace("{", "\x02")
            # text = text.replace("}", "{")
            # text = text.replace("\x02", "}")
            try:
                if not re.search(r'[\uFB50-\uFDFF\uFE70-\uFEFF]', text):
                    # Reshape Arabic text for proper character joining
                    from arabic_reshaper import ArabicReshaper
                    configuration = {
                        'delete_harakat': False,  # Keep diacritical marks
                        'support_ligatures': True,  # Support Arabic ligatures
                        'RIAL SIGN': True,
                        'ARABIC COMMA': True,
                        'ARABIC SEMICOLON': True,
                        'ARABIC QUESTION MARK': True,
                        'ZWNJ': True,  # Zero Width Non-Joiner
                    }

                    reshaper = ArabicReshaper(configuration=configuration)
                    reshaped_text = reshaper.reshape(text)
                    display_text = get_display(reshaped_text, base_dir='R')
                else:
                    display_text = text
                return display_text
            except Exception as e:
                logger.warning(f"Failed to shape Arabic text: {e}")
                return text

        return text

    def _find_optimal_scale_and_layout(
        self,
        paragraph: il_version_1.PdfParagraph,
        page: il_version_1.Page,
        typesetting_units: list[TypesettingUnit],
        initial_scale: float = 1.0,
        use_english_line_break: bool = True,
        apply_layout: bool = False,
    ) -> tuple[float, list[TypesettingUnit] | None]:
        """Ã¦Å¸Â¥Ã¦â€°Â¾Ã¦Å“â‚¬Ã¤Â¼ËœÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¥Â¹Â¶Ã¥ÂÂ¯Ã©â‚¬â€°Ã¦â€¹Â©Ã¦â‚¬Â§Ã¥Å“Â°Ã¦â€°Â§Ã¨Â¡Å’Ã¥Â¸Æ’Ã¥Â±â‚¬

        Args:
            paragraph: Ã¦Â®ÂµÃ¨ÂÂ½Ã¥Â¯Â¹Ã¨Â±Â¡
            page: Ã©Â¡ÂµÃ©ÂÂ¢Ã¥Â¯Â¹Ã¨Â±Â¡
            typesetting_units: Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€”Ã¨Â¡Â¨
            initial_scale: Ã¥Ë†ÂÃ¥Â§â€¹Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
            use_english_line_break: Ã¦ËœÂ¯Ã¥ÂÂ¦Ã¤Â½Â¿Ã§â€Â¨Ã¨â€¹Â±Ã¦â€“â€¡Ã¦ÂÂ¢Ã¨Â¡Å’Ã¨Â§â€žÃ¥Ë†â„¢
            apply_layout: Ã¦ËœÂ¯Ã¥ÂÂ¦Ã¥Âºâ€Ã§â€Â¨Ã¥Â¸Æ’Ã¥Â±â‚¬Ã¥Ë†Â° paragraphÃ¯Â¼Ë†True Ã¦â€”Â¶Ã¦â€°Â§Ã¨Â¡Å’Ã¥Â®Å¾Ã©â„¢â€¦Ã¦Å½â€™Ã§â€°Ë†Ã¯Â¼â€°

        Returns:
            tuple[float, list[TypesettingUnit] | None]: (Ã¦Å“â‚¬Ã§Â»Ë†Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¯Â¼Å’Ã¦Å½â€™Ã§â€°Ë†Ã¥ÂÅ½Ã§Å¡â€žÃ¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€”Ã¨Â¡Â¨Ã¦Ë†â€“ None)
        """
        if not paragraph.box:
            return initial_scale, None

        box = paragraph.box
        scale = initial_scale
        line_skip = 1.50 if self.is_cjk else 1.3
        min_scale = 0.1
        expand_space_flag = 0
        final_typeset_units = None

        while scale >= min_scale:
            try:
                # Ã¥Â°ÂÃ¨Â¯â€¢Ã¥Â¸Æ’Ã¥Â±â‚¬Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’
                typeset_units, all_units_fit = self._layout_typesetting_units(
                    typesetting_units,
                    box,
                    scale,
                    line_skip,
                    paragraph,
                    use_english_line_break,
                )

                # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦â€°â‚¬Ã¦Å“â€°Ã¥Ââ€¢Ã¥â€¦Æ’Ã©Æ’Â½Ã¦â€Â¾Ã¥Â¾â€”Ã¤Â¸â€¹
                if all_units_fit:
                    if apply_layout:
                        # Ã¥Â®Å¾Ã©â„¢â€¦Ã¥Âºâ€Ã§â€Â¨Ã¦Å½â€™Ã§â€°Ë†Ã§Â»â€œÃ¦Å¾Å“
                        paragraph.scale = scale
                        paragraph.pdf_paragraph_composition = []
                        for unit in typeset_units:
                            chars, curves, forms = unit.render()
                            for char in chars:
                                paragraph.pdf_paragraph_composition.append(
                                    PdfParagraphComposition(pdf_character=char),
                                )
                            for curve in curves:
                                page.pdf_curve.append(curve)
                            for form in forms:
                                page.pdf_form.append(form)
                        final_typeset_units = typeset_units
                    return scale, final_typeset_units
            except Exception:
                # Ã¥Â¦â€šÃ¦Å¾Å“Ã¥Â¸Æ’Ã¥Â±â‚¬Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¥â€¡ÂºÃ©â€â„¢Ã¯Â¼Å’Ã§Â»Â§Ã§Â»Â­Ã¥Â°ÂÃ¨Â¯â€¢Ã¤Â¸â€¹Ã¤Â¸â‚¬Ã¤Â¸ÂªÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
                pass

            # Ã¦Â·Â»Ã¥Å Â Ã¤Â¸Å½Ã¥Å½Å¸ retypeset Ã¤Â¸â‚¬Ã¨â€¡Â´Ã§Å¡â€žÃ©â‚¬Â»Ã¨Â¾â€˜Ã¦Â£â‚¬Ã¦Å¸Â¥
            if not hasattr(paragraph, "debug_id") or not paragraph.debug_id:
                return scale, final_typeset_units

            # Ã¥â€¡ÂÃ¥Â°ÂÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
            if scale > 0.6:
                scale -= 0.05
            else:
                scale -= 0.1

            if scale < 0.7:
                space_expanded = False  # Ã¦Â â€¡Ã¨Â®Â°Ã¦ËœÂ¯Ã¥ÂÂ¦Ã¦Ë†ÂÃ¥Å Å¸Ã¦â€°Â©Ã¥Â±â€¢Ã¤Âºâ€ Ã§Â©ÂºÃ©â€”Â´

                if expand_space_flag == 0:
                    # Ã¥Â°ÂÃ¨Â¯â€¢Ã¥Ââ€˜Ã¤Â¸â€¹Ã¦â€°Â©Ã¥Â±â€¢
                    try:
                        min_y = self.get_max_bottom_space(box, page) + 2
                        if min_y < box.y:
                            expanded_box = Box(x=box.x, y=min_y, x2=box.x2, y2=box.y2)
                            box = expanded_box
                            if apply_layout:
                                # Ã¦â€ºÂ´Ã¦â€“Â°Ã¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¨Â¾Â¹Ã§â€¢Å’Ã¦Â¡â€ 
                                paragraph.box = expanded_box
                            space_expanded = True
                    except Exception:
                        pass
                    expand_space_flag = 1

                    # Ã¥ÂÂªÃ¦Å“â€°Ã¦Ë†ÂÃ¥Å Å¸Ã¦â€°Â©Ã¥Â±â€¢Ã§Â©ÂºÃ©â€”Â´Ã¦â€”Â¶Ã¦â€°Â continueÃ¯Â¼Å’Ã¥ÂÂ¦Ã¥Ë†â„¢Ã§Â»Â§Ã§Â»Â­Ã¥â€¡ÂÃ¥Â°Â scale
                    if space_expanded:
                        continue

                elif expand_space_flag == 1:
                    # Ã¥Â°ÂÃ¨Â¯â€¢Ã¥Ââ€˜Ã¥ÂÂ³Ã¦â€°Â©Ã¥Â±â€¢
                    try:
                        max_x = self.get_max_right_space(box, page) - 5
                        if max_x > box.x2:
                            expanded_box = Box(x=box.x, y=box.y, x2=max_x, y2=box.y2)
                            box = expanded_box
                            if apply_layout:
                                # Ã¦â€ºÂ´Ã¦â€“Â°Ã¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¨Â¾Â¹Ã§â€¢Å’Ã¦Â¡â€ 
                                paragraph.box = expanded_box
                            space_expanded = True
                    except Exception:
                        pass
                    expand_space_flag = 2

                    # Ã¥ÂÂªÃ¦Å“â€°Ã¦Ë†ÂÃ¥Å Å¸Ã¦â€°Â©Ã¥Â±â€¢Ã§Â©ÂºÃ©â€”Â´Ã¦â€”Â¶Ã¦â€°Â continueÃ¯Â¼Å’Ã¥ÂÂ¦Ã¥Ë†â„¢Ã§Â»Â§Ã§Â»Â­Ã¥â€¡ÂÃ¥Â°Â scale
                    if space_expanded:
                        continue

                # Ã¥ÂÂªÃ¦Å“â€°Ã¥Å“Â¨Ã¦â€°Â©Ã¥Â±â€¢Ã¥Â°ÂÃ¨Â¯â€¢Ã©ËœÂ¶Ã¦Â®Âµ (expand_space_flag < 2) Ã¤Â¸â€Ã¦â€°Â©Ã¥Â±â€¢Ã¥Â¤Â±Ã¨Â´Â¥Ã¦â€”Â¶Ã¦â€°ÂÃ©â€¡ÂÃ§Â½Â® scale
                # Ã¥Â½â€œ expand_space_flag >= 2 Ã¦â€”Â¶Ã¯Â¼Å’Ã¨Â¯Â´Ã¦ËœÅ½Ã¥Â·Â²Ã§Â»ÂÃ¥Â°ÂÃ¨Â¯â€¢Ã¨Â¿â€¡Ã¦â€°â‚¬Ã¦Å“â€°Ã¦â€°Â©Ã¥Â±â€¢Ã¯Â¼Å’Ã¥Âºâ€Ã¨Â¯Â¥Ã§Â»Â§Ã§Â»Â­Ã¦Â­Â£Ã¥Â¸Â¸Ã§Å¡â€ž scale Ã¥â€¡ÂÃ¥Â°Â
                if expand_space_flag < 2:
                    # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦â€”Â Ã¦Â³â€¢Ã¦â€°Â©Ã¥Â±â€¢Ã§Â©ÂºÃ©â€”Â´Ã¯Â¼Å’Ã©â€¡ÂÃ§Â½Â® scale Ã¥Â¹Â¶Ã§Â»Â§Ã§Â»Â­Ã¥Â¾ÂªÃ§Å½Â¯
                    scale = 1.0

        # Ã¥Â¦â€šÃ¦Å¾Å“Ã¤Â»ÂÃ§â€žÂ¶Ã¦â€Â¾Ã¤Â¸ÂÃ¤Â¸â€¹Ã¯Â¼Å’Ã¥Â°ÂÃ¨Â¯â€¢Ã¥Å½Â»Ã©â„¢Â¤Ã¨â€¹Â±Ã¦â€“â€¡Ã¦ÂÂ¢Ã¨Â¡Å’Ã©â„¢ÂÃ¥Ë†Â¶
        if use_english_line_break:
            return self._find_optimal_scale_and_layout(
                paragraph,
                page,
                typesetting_units,
                initial_scale,
                use_english_line_break=False,
                apply_layout=apply_layout,
            )

        # Ã¦Å“â‚¬Ã¥ÂÅ½Ã¨Â¿â€Ã¥â€ºÅ¾Ã¦Å“â‚¬Ã¥Â°ÂÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â
        return min_scale, final_typeset_units

    def _get_optimal_scale(
        self,
        paragraph: il_version_1.PdfParagraph,
        page: il_version_1.Page,
        typesetting_units: list[TypesettingUnit],
        use_english_line_break: bool = True,
    ) -> float:
        """Ã¨Å½Â·Ã¥Ââ€“Ã¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¦Å“â‚¬Ã¤Â¼ËœÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¯Â¼Å’Ã¤Â¸ÂÃ¦â€°Â§Ã¨Â¡Å’Ã¥Â®Å¾Ã©â„¢â€¦Ã¦Å½â€™Ã§â€°Ë†"""
        scale, _ = self._find_optimal_scale_and_layout(
            paragraph,
            page,
            typesetting_units,
            1.0,
            use_english_line_break,
            apply_layout=False,
        )
        return scale

    def retypeset_with_precomputed_scale(
        self,
        paragraph: il_version_1.PdfParagraph,
        page: il_version_1.Page,
        typesetting_units: list[TypesettingUnit],
        precomputed_scale: float,
        use_english_line_break: bool = True,
    ):
        """Ã¤Â½Â¿Ã§â€Â¨Ã©Â¢â€žÃ¨Â®Â¡Ã§Â®â€”Ã§Å¡â€žÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¨Â¿â€ºÃ¨Â¡Å’Ã¦Å½â€™Ã§â€°Ë†"""
        if not paragraph.box:
            return

        # Ã¤Â½Â¿Ã§â€Â¨Ã©â‚¬Å¡Ã§â€Â¨Ã¦â€“Â¹Ã¦Â³â€¢Ã¨Â¿â€ºÃ¨Â¡Å’Ã¦Å½â€™Ã§â€°Ë†Ã¯Â¼Å’Ã¤Â¼Â Ã¥â€¦Â¥Ã©Â¢â€žÃ¨Â®Â¡Ã§Â®â€”Ã§Å¡â€žÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¤Â½Å“Ã¤Â¸ÂºÃ¥Ë†ÂÃ¥Â§â€¹Ã¥â‚¬Â¼
        self._find_optimal_scale_and_layout(
            paragraph,
            page,
            typesetting_units,
            precomputed_scale,
            use_english_line_break,
            apply_layout=True,
        )

    def typesetting_document(self, document: il_version_1.Document):
        # Add detailed logging at the start
        if self.detailed_logger:
            self.detailed_logger.log_step("Typesetting Started")
        
        # ÃƒÂ¥Ã…Â½Ã…Â¸ÃƒÂ¦Ã…â€œÃ¢â‚¬Â°ÃƒÂ§Ã…Â¡Ã¢â‚¬Å¾ÃƒÂ¦Ã…Â½'ÃƒÂ§Ã¢â‚¬Â°Ã‹â€ ÃƒÂ©Ã¢â€šÂ¬Ã‚Â»ÃƒÂ¨Ã‚Â¾'
        if self.translation_config.progress_monitor:
            with self.translation_config.progress_monitor.stage_start(
                self.stage_name,
                len(document.page) * 2,
            ) as pbar:
                # ÃƒÂ©Ã‚Â¢Ã¢â‚¬Å¾ÃƒÂ¥Ã‚Â¤Ã¢â‚¬Å¾ÃƒÂ§Ã¢â‚¬Â ÃƒÂ¯Ã‚Â¼Ã…Â¡ÃƒÂ¨Ã…Â½Ã‚Â·ÃƒÂ¥Ã¢â‚¬â€œÃƒÂ¦Ã¢â‚¬Â°Ã¢â€šÂ¬ÃƒÂ¦Ã…â€œÃ¢â‚¬Â°ÃƒÂ¦Ã‚Â®Ã‚ÂµÃƒÂ¨Ã‚Â½ÃƒÂ§Ã…Â¡Ã¢â‚¬Å¾ÃƒÂ¦Ã…â€œÃ¢â€šÂ¬ÃƒÂ¤Ã‚Â¼Ã‹Å“ÃƒÂ§Ã‚Â¼Ã‚Â©ÃƒÂ¦"Ã‚Â¾ÃƒÂ¥Ã¢â‚¬Âº ÃƒÂ¥Ã‚Â­
                self.preprocess_document(document, pbar)

                for page_idx, page in enumerate(document.page):
                    self.translation_config.raise_if_cancelled()
                    
                    # Add detailed logging for each page
                    if self.detailed_logger:
                        self.detailed_logger.log_step(
                            f"Typesetting Page {page_idx + 1}",
                            f"Paragraphs to typeset: {len(page.pdf_paragraph) if hasattr(page, 'pdf_paragraph') else 0}"
                        )
                    
                    self.render_page(page)
                    pbar.advance()
        else:
            for page_idx, page in enumerate(document.page):
                self.translation_config.raise_if_cancelled()
                
                # Add detailed logging for each page
                if self.detailed_logger:
                    self.detailed_logger.log_step(
                        f"Typesetting Page {page_idx + 1}",
                        f"Paragraphs to typeset: {len(page.pdf_paragraph) if hasattr(page, 'pdf_paragraph') else 0}"
                    )
                
                self.render_page(page)
        
        # Add detailed logging at the end
        if self.detailed_logger:
            self.detailed_logger.log_step("Typesetting Complete")

    def render_page(self, page: il_version_1.Page):
        fonts: dict[
            str | int,
            il_version_1.PdfFont | dict[str, il_version_1.PdfFont],
        ] = {f.font_id: f for f in page.pdf_font if f.font_id}
        page_fonts = {f.font_id: f for f in page.pdf_font if f.font_id}
        for k, v in self.font_mapper.fontid2font.items():
            fonts[k] = v
        for xobj in page.pdf_xobject:
            if xobj.xobj_id is not None:
                fonts[xobj.xobj_id] = page_fonts.copy()
                for font in xobj.pdf_font:
                    if font.font_id:
                        fonts[xobj.xobj_id][font.font_id] = font
        if (
            page.page_number == 0
            and self.translation_config.watermark_output_mode
            == WatermarkOutputMode.Watermarked
        ):
            self.add_watermark(page)
        try:
            para_index = index.Index()
            para_map = {}
            #
            valid_paras = [
                p
                for p in page.pdf_paragraph
                if p.box
                and all(c is not None for c in [p.box.x, p.box.y, p.box.x2, p.box.y2])
            ]

            for i, para in enumerate(valid_paras):
                para_map[i] = para
                para_index.insert(i, box_to_tuple(para.box))

            for i, p_upper in para_map.items():
                if not (p_upper.box and p_upper.box.y is not None):
                    continue

                # Calculate paragraph height and set required gap accordingly
                para_height = p_upper.box.y2 - p_upper.box.y
                required_gap = 0.5 if para_height < 36 else 3

                check_area = il_version_1.Box(
                    x=p_upper.box.x,
                    y=p_upper.box.y - required_gap,
                    x2=p_upper.box.x2,
                    y2=p_upper.box.y,
                )

                candidate_ids = list(para_index.intersection(box_to_tuple(check_area)))

                conflicting_paras = []
                for para_id in candidate_ids:
                    if para_id == i:
                        continue
                    p_lower = para_map[para_id]
                    if not (
                        p_lower.box
                        and p_upper.box
                        and p_lower.box.x2 < p_upper.box.x
                        or p_lower.box.x > p_upper.box.x2
                    ):
                        conflicting_paras.append(p_lower)

                if conflicting_paras:
                    max_y2 = max(
                        p.box.y2
                        for p in conflicting_paras
                        if p.box and p.box.y2 is not None
                    )

                    new_y = max_y2 + required_gap
                    if p_upper.box and new_y < p_upper.box.y2:
                        p_upper.box.y = new_y
        except Exception as e:
            logger.warning(
                f"Failed to adjust paragraph positions on page {page.page_number}: {e}"
            )
        # Ã¥Â¼â‚¬Ã¥Â§â€¹Ã¥Â®Å¾Ã©â„¢â€¦Ã§Å¡â€žÃ¦Â¸Â²Ã¦Å¸â€œÃ¨Â¿â€¡Ã§Â¨â€¹
        for paragraph in page.pdf_paragraph:
            self.render_paragraph(paragraph, page, fonts)

    def add_watermark(self, page: il_version_1.Page):
        page_width = page.cropbox.box.x2 - page.cropbox.box.x
        page_height = page.cropbox.box.y2 - page.cropbox.box.y
        style = il_version_1.PdfStyle(
            font_id="base",
            font_size=6,
            graphic_state=il_version_1.GraphicState(),
        )
        text = f"BabelDOC {WATERMARK_VERSION} (http://yadt.io)"
        if self.translation_config.debug:
            text += "\n "
        page.pdf_paragraph.append(
            il_version_1.PdfParagraph(
                first_line_indent=False,
                box=il_version_1.Box(
                    x=page.cropbox.box.x + page_width * 0.05,
                    y=page.cropbox.box.y,
                    x2=page.cropbox.box.x2,
                    y2=page.cropbox.box.y2 - page_height * 0.05,
                ),
                vertical=False,
                pdf_style=style,
                pdf_paragraph_composition=[
                    il_version_1.PdfParagraphComposition(
                        pdf_same_style_unicode_characters=il_version_1.PdfSameStyleUnicodeCharacters(
                            unicode=text,
                            pdf_style=style,
                        ),
                    ),
                ],
                xobj_id=-1,
            ),
        )

    def render_paragraph(
        self,
        paragraph: il_version_1.PdfParagraph,
        page: il_version_1.Page,
        fonts: dict[
            str | int,
            il_version_1.PdfFont | dict[str, il_version_1.PdfFont],
        ],
    ):
        typesetting_units = self.create_typesetting_units(paragraph, fonts)
        # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦â€°â‚¬Ã¦Å“â€°Ã¥Ââ€¢Ã¥â€¦Æ’Ã©Æ’Â½Ã¥ÂÂ¯Ã¤Â»Â¥Ã§â€ºÂ´Ã¦Å½Â¥Ã¤Â¼Â Ã©â‚¬â€™Ã¯Â¼Å’Ã¥Ë†â„¢Ã§â€ºÂ´Ã¦Å½Â¥Ã¤Â¼Â Ã©â‚¬â€™
        if all(unit.can_passthrough for unit in typesetting_units):
            paragraph.scale = 1.0
            paragraph.pdf_paragraph_composition = self.create_passthrough_composition(
                typesetting_units,
            )
        else:
            # Ã¤Â½Â¿Ã§â€Â¨Ã©Â¢â€žÃ¨Â®Â¡Ã§Â®â€”Ã§Å¡â€žÃ§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­ÂÃ¨Â¿â€ºÃ¨Â¡Å’Ã©â€¡ÂÃ¦Å½â€™Ã§â€°Ë†
            precomputed_scale = (
                paragraph.optimal_scale if paragraph.optimal_scale is not None else 1.0
            )

            # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦Å“â€°Ã¥Ââ€¢Ã¥â€¦Æ’Ã¦â€”Â Ã¦Â³â€¢Ã§â€ºÂ´Ã¦Å½Â¥Ã¤Â¼Â Ã©â‚¬â€™Ã¯Â¼Å’Ã¥Ë†â„¢Ã¨Â¿â€ºÃ¨Â¡Å’Ã©â€¡ÂÃ¦Å½â€™Ã§â€°Ë†
            paragraph.pdf_paragraph_composition = []
            self.retypeset_with_precomputed_scale(
                paragraph, page, typesetting_units, precomputed_scale
            )

            # Ã©â€¡ÂÃ¦Å½â€™Ã§â€°Ë†Ã¥ÂÅ½Ã¯Â¼Å’Ã©â€¡ÂÃ¦â€“Â°Ã¨Â®Â¾Ã§Â½Â®Ã¦Â®ÂµÃ¨ÂÂ½Ã¥Ââ€žÃ¥Â­â€”Ã§Â¬Â¦Ã§Å¡â€ž render order
            self._update_paragraph_render_order(paragraph)

    def _is_arabic_char(self, char: str) -> bool:
        """Check if character is Arabic - OPTIMIZED"""
        if not char:
            return False
        try:
            code_point = ord(char[0])
            return (0x0600 <= code_point <= 0x06FF) or (0xFB50 <= code_point <= 0xFDFF) or (0xFE70 <= code_point <= 0xFEFF)
        except:
            return False

    def _layout_typesetting_units(
        self,
        typesetting_units: list[TypesettingUnit],
        box: Box,
        scale: float,
        line_skip: float,
        paragraph: il_version_1.PdfParagraph,
        use_english_line_break: bool = True,
    ) -> tuple[list[TypesettingUnit], bool]:
        """布局排版单元 - OPTIMIZED FOR ARABIC RTL"""
        
        # Detect Arabic FIRST
        lang_out = (self.translation_config.lang_out or "").lower()
        is_arabic = any(marker in lang_out for marker in ["ar", "arabic", "ara"])
        
        # 计算字体大小
        font_sizes = []
        for unit in typesetting_units:
            if unit.font_size:
                font_sizes.append(unit.font_size)
            if unit.char and unit.char.pdf_style and unit.char.pdf_style.font_size:
                font_sizes.append(unit.char.pdf_style.font_size)
        if not font_sizes:
            font_sizes = [12]
        font_sizes.sort()
        font_size = statistics.mode(font_sizes)

        space_width = (
            self.font_mapper.base_font.char_lengths("你 ", font_size * scale)[0] * 0.5
        )

        # 计算行高
        unit_heights = [unit.height for unit in typesetting_units] if typesetting_units else []
        if not unit_heights:
            avg_height = 0
        elif len(unit_heights) == 1:
            avg_height = unit_heights[0] * scale
        else:
            try:
                avg_height = statistics.mode(unit_heights) * scale
            except statistics.StatisticsError:
                avg_height = sum(unit_heights) / len(unit_heights) * scale

        # 初始化
        current_x = box.x
        current_y = box.y2 - avg_height
        box = copy.deepcopy(box)
        line_height = 0
        current_line_heights = []
        typeset_units = []
        all_units_fit = True
        last_unit: TypesettingUnit | None = None
        line_ys = [current_y]
        
        if paragraph.first_line_indent:
            current_x += space_width * 4
        
        # OPTIMIZED ARABIC WORD-LEVEL PROCESSING
        if is_arabic:
            i = 0
            safety_counter = 0
            max_iterations = len(typesetting_units) * 2  # Safety limit
            
            while i < len(typesetting_units) and safety_counter < max_iterations:
                safety_counter += 1
                
                # Collect word (simple: until space or end)
                word_units = []
                while i < len(typesetting_units):
                    unit = typesetting_units[i]
                    if unit.is_space:
                        if word_units:
                            i += 1
                        break
                    word_units.append(unit)
                    i += 1
                    if len(word_units) > 100:  # Safety: max word length
                        break
                
                if not word_units:
                    continue
                
                # Calculate word width
                word_width = sum(u.width * scale for u in word_units)
                
                # Skip leading spaces
                if current_x == box.x and word_units and word_units[0].is_space:
                    continue
                
                # Check if needs new line
                if current_x + word_width > box.x2 and current_x > box.x:
                    current_x = box.x
                    if current_line_heights:
                        max_height = max(current_line_heights)
                        mode_height = statistics.mode(current_line_heights) if len(current_line_heights) > 1 else max_height
                        current_y -= max(mode_height * line_skip, max_height * 1.05)
                        line_ys.append(current_y)
                        current_line_heights = []
                    
                    if current_y < box.y:
                        all_units_fit = False
                
                # Place word units
                for unit in word_units:
                    if unit.is_space and current_x == box.x:
                        continue
                    
                    unit_width = unit.width * scale
                    unit_height = unit.height * scale
                    
                    # CJK spacing
                    if (last_unit and last_unit.is_cjk_char ^ unit.is_cjk_char 
                        and not unit.is_space and current_x > box.x):
                        current_x += space_width * 0.5
                    
                    relocated_unit = unit.relocate(current_x, current_y, scale)
                    typeset_units.append(relocated_unit)
                    
                    if not unit.is_space:
                        current_line_heights.append(unit_height)
                    
                    current_x = relocated_unit.box.x2
                    last_unit = relocated_unit
            
            # Right-align Arabic lines
            if typeset_units:
                lines_dict = {}
                for unit in typeset_units:
                    if unit.box and unit.box.y is not None:
                        line_y = round(unit.box.y, 1)
                        if line_y not in lines_dict:
                            lines_dict[line_y] = []
                        lines_dict[line_y].append(unit)
                
                for line_y, line_units in lines_dict.items():
                    if line_units:
                        line_max_x = max(u.box.x2 for u in line_units if u.box and u.box.x2 is not None)
                        shift_x = box.x2 - line_max_x
                        
                        for unit in line_units:
                            if unit.box:
                                unit.box.x += shift_x
                                unit.box.x2 += shift_x
                            if unit.x is not None:
                                unit.x += shift_x
                            if unit.char and unit.char.box:
                                unit.char.box.x += shift_x
                                unit.char.box.x2 += shift_x
                            if unit.char and unit.char.visual_bbox and unit.char.visual_bbox.box:
                                unit.char.visual_bbox.box.x += shift_x
                                unit.char.visual_bbox.box.x2 += shift_x
        else:
            # ORIGINAL NON-ARABIC LOGIC (UNCHANGED)
            for i, unit in enumerate(typesetting_units):
                unit_width = unit.width * scale
                unit_height = unit.height * scale

                if current_x == box.x and unit.is_space:
                    continue

                if (last_unit and last_unit.is_cjk_char ^ unit.is_cjk_char
                    and last_unit.box and last_unit.box.y
                    and current_y - 0.1 <= last_unit.box.y2 <= current_y + line_height + 0.1
                    and not last_unit.mixed_character_blacklist and not unit.mixed_character_blacklist
                    and current_x > box.x and unit.try_get_unicode() != " "
                    and last_unit.try_get_unicode() != " "
                    and last_unit.try_get_unicode() not in ["。", "，", "、", "；", "！", "？"]):
                    current_x += space_width * 0.5
                
                if use_english_line_break:
                    width_before_next_break_point = self._get_width_before_next_break_point(typesetting_units[i:], scale)
                else:
                    width_before_next_break_point = 0

                if not unit.is_hung_punctuation and (
                    (current_x + unit_width > box.x2) or
                    (use_english_line_break and current_x + unit_width + width_before_next_break_point > box.x2) or
                    (unit.is_cannot_appear_in_line_end_punctuation and current_x + unit_width * 2 > box.x2)):
                    
                    current_x = box.x
                    if not current_line_heights:
                        return [], False
                    max_height = max(current_line_heights)
                    mode_height = statistics.mode(current_line_heights)
                    current_y -= max(mode_height * line_skip, max_height * 1.05)
                    line_ys.append(current_y)
                    line_height = 0.0
                    current_line_heights = []

                    if current_y < box.y:
                        all_units_fit = False

                    if unit.is_space:
                        line_height = max(line_height, unit_height)
                        continue

                relocated_unit = unit.relocate(current_x, current_y, scale)
                typeset_units.append(relocated_unit)

                if not unit.is_space:
                    current_line_heights.append(unit_height)

                prev_x = current_x
                current_x = relocated_unit.box.x2
                if prev_x > current_x:
                    logger.warning(f"坐标回退！！！TypesettingUnit: {unit.box}, ")

                last_unit = relocated_unit
                    # If Arabic, reverse the line order
        if is_arabic and typeset_units:
            # Group units by line (using Y coordinates)
            lines_dict = {}
            for unit in typeset_units:
                if unit.box and unit.box.y is not None:
                    # Round Y coordinate to group units on the same line
                    line_y = round(unit.box.y, 1)
                    if line_y not in lines_dict:
                        lines_dict[line_y] = []
                    lines_dict[line_y].append(unit)
            
            # Sort lines by Y coordinate (top to bottom) and reverse
            sorted_line_ys = sorted(lines_dict.keys(), reverse=True)
            
            # Rebuild typeset_units with reversed line order
            reversed_typeset_units = []
            for line_y in reversed(sorted_line_ys):
                reversed_typeset_units.extend(lines_dict[line_y])
            
            # Now reposition all units to swap their Y coordinates
            # Map old Y positions to new Y positions
            y_mapping = {}
            for i, old_y in enumerate(sorted_line_ys):
                new_y = sorted_line_ys[len(sorted_line_ys) - 1 - i]
                y_mapping[old_y] = new_y
            
            # Update Y coordinates for all units
            for unit in reversed_typeset_units:
                if unit.box and unit.box.y is not None:
                    old_y = round(unit.box.y, 1)
                    if old_y in y_mapping:
                        new_y = y_mapping[old_y]
                        y_diff = new_y - old_y
                        # Update the unit's Y position
                        if unit.y is not None:
                            unit.y += y_diff
                        if unit.box:
                            unit.box.y += y_diff
                            unit.box.y2 += y_diff
            
            typeset_units = reversed_typeset_units
        
        return typeset_units, all_units_fit

# CORRECT FIX FOR ARABIC TEXT LAYOUT
# Replace the _layout_typesetting_units function in typesetting.py (lines 1346-1502)

    # def _layout_typesetting_units(
    #         self,
    #         typesetting_units: list[TypesettingUnit],
    #         box: Box,
    #         scale: float,
    #         line_skip: float,
    #         paragraph: il_version_1.PdfParagraph,
    #         use_english_line_break: bool = True,
    #     ) -> tuple[list[TypesettingUnit], bool]:
    #         """Ã¥Â¸Æ’Ã¥Â±â‚¬Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã£â‚¬â€š

    #         Args:
    #             typesetting_units: Ã¨Â¦ÂÃ¥Â¸Æ’Ã¥Â±â‚¬Ã§Å¡â€žÃ¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€”Ã¨Â¡Â¨
    #             box: Ã¥Â¸Æ’Ã¥Â±â‚¬Ã¨Â¾Â¹Ã§â€¢Å’Ã¦Â¡â€ 
    #             scale: Ã§Â¼Â©Ã¦â€Â¾Ã¥â€ºÂ Ã¥Â­Â

    #         Returns:
    #             tuple[list[TypesettingUnit], bool]: (Ã¥Â·Â²Ã¥Â¸Æ’Ã¥Â±â‚¬Ã§Å¡â€žÃ¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€”Ã¨Â¡Â¨Ã¯Â¼Å’Ã¦ËœÂ¯Ã¥ÂÂ¦Ã¦â€°â‚¬Ã¦Å“â€°Ã¥Ââ€¢Ã¥â€¦Æ’Ã©Æ’Â½Ã¦â€Â¾Ã¥Â¾â€”Ã¤Â¸â€¹)
    #         """
    #         # Ã¨Â®Â¡Ã§Â®â€”Ã¥Â­â€”Ã¥ÂÂ·Ã¤Â¼â€”Ã¦â€¢Â°
    #         font_sizes = []
    #         for unit in typesetting_units:
    #             if unit.font_size:
    #                 font_sizes.append(unit.font_size)
    #             if unit.char and unit.char.pdf_style and unit.char.pdf_style.font_size:
    #                 font_sizes.append(unit.char.pdf_style.font_size)
    #         font_sizes.sort()
    #         font_size = statistics.mode(font_sizes)

    #         space_width = (
    #             self.font_mapper.base_font.char_lengths("Ã¤Â½Â  ", font_size * scale)[0] * 0.5
    #         )

    #         # Ã¨Â®Â¡Ã§Â®â€”Ã¨Â¡Å’Ã©Â«ËœÃ¯Â¼Ë†Ã¤Â½Â¿Ã§â€Â¨Ã¤Â¼â€”Ã¦â€¢Â°Ã¯Â¼â€°
    #         unit_heights = (
    #             [unit.height for unit in typesetting_units] if typesetting_units else []
    #         )
    #         if not unit_heights:
    #             avg_height = 0
    #         elif len(unit_heights) == 1:
    #             avg_height = unit_heights[0] * scale
    #         else:
    #             try:
    #                 avg_height = statistics.mode(unit_heights) * scale
    #             except statistics.StatisticsError:
    #                 # Ã¥Â¦â€šÃ¦Å¾Å“Ã¦Â²Â¡Ã¦Å“â€°Ã¤Â¼â€”Ã¦â€¢Â°Ã¯Â¼Ë†Ã¦â€°â‚¬Ã¦Å“â€°Ã¥â‚¬Â¼Ã©Æ’Â½Ã¥â€¡ÂºÃ§Å½Â°Ã§â€ºÂ¸Ã¥ÂÅ’Ã¦Â¬Â¡Ã¦â€¢Â°Ã¯Â¼â€°Ã¯Â¼Å’Ã¥Ë†â„¢Ã¤Â½Â¿Ã§â€Â¨Ã¥Â¹Â³Ã¥Ââ€¡Ã¥â‚¬Â¼
    #                 avg_height = sum(unit_heights) / len(unit_heights) * scale

    #         # *** NEW: Detect Arabic language ***
    #         lang_out = (self.translation_config.lang_out or "").lower()
    #         is_arabic = False
    #         if lang_out in ("en-ar", "ar", "ara", "arabic"):
    #             is_arabic = True
    #         elif "-ar" in lang_out or "->ar" in lang_out or "/ar" in lang_out:
    #             is_arabic = True

    #         # Ã¥Ë†ÂÃ¥Â§â€¹Ã¥Å’â€“Ã¤Â½ÂÃ§Â½Â®Ã¤Â¸ÂºÃ¥ÂÂ³Ã¤Â¸Å Ã¨Â§â€™Ã¯Â¼Å’Ã¥Â¹Â¶Ã¥â€¡ÂÃ¥Å½Â»Ã¤Â¸â‚¬Ã¤Â¸ÂªÃ¥Â¹Â³Ã¥Ââ€¡Ã¨Â¡Å’Ã©Â«Ëœ
    #         # *** CHANGED: For Arabic, calculate total line width first and start from right ***
    #         current_x = box.x
    #         current_y = box.y2 - avg_height
    #         box = copy.deepcopy(box)
    #         line_height = 0
    #         current_line_heights = []  # Ã¥Â­ËœÃ¥â€šÂ¨Ã¥Â½â€œÃ¥â€°ÂÃ¨Â¡Å’Ã¦â€°â‚¬Ã¦Å“â€°Ã¥â€¦Æ’Ã§Â´Â Ã§Å¡â€žÃ©Â«ËœÃ¥ÂºÂ¦

    #         # Ã¥Â­ËœÃ¥â€šÂ¨Ã¥Â·Â²Ã¦Å½â€™Ã§â€°Ë†Ã§Å¡â€žÃ¥Ââ€¢Ã¥â€¦Æ’
    #         typeset_units = []
    #         all_units_fit = True
    #         last_unit: TypesettingUnit | None = None
    #         line_ys = [current_y]
    #         if paragraph.first_line_indent:
    #             current_x += space_width * 4
    #         # Ã©ÂÂÃ¥Å½â€ Ã¦â€°â‚¬Ã¦Å“â€°Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’
    #         for i, unit in enumerate(typesetting_units):
    #             # Ã¨Â®Â¡Ã§Â®â€”Ã¥Â½â€œÃ¥â€°ÂÃ¥Ââ€¢Ã¥â€¦Æ’Ã¥Å“Â¨Ã¥Â½â€œÃ¥â€°ÂÃ§Â¼Â©Ã¦â€Â¾Ã¤Â¸â€¹Ã§Å¡â€žÃ¥Â°ÂºÃ¥Â¯Â¸
    #             unit_width = unit.width * scale
    #             unit_height = unit.height * scale

    #             # Ã¨Â·Â³Ã¨Â¿â€¡Ã¨Â¡Å’Ã©Â¦â€“Ã§Å¡â€žÃ§Â©ÂºÃ¦Â Â¼
    #             if current_x == box.x and unit.is_space:
    #                 continue

    #             if (
    #                 last_unit  # Ã¦Å“â€°Ã¤Â¸Å Ã¤Â¸â‚¬Ã¤Â¸ÂªÃ¥Ââ€¢Ã¥â€¦Æ’
    #                 and last_unit.is_cjk_char ^ unit.is_cjk_char  # Ã¤Â¸Â­Ã¨â€¹Â±Ã¦â€“â€¡Ã¤ÂºÂ¤Ã§â€¢Å’Ã¥Â¤â€ž
    #                 and (
    #                     last_unit.box
    #                     and last_unit.box.y
    #                     and current_y - 0.1
    #                     <= last_unit.box.y2
    #                     <= current_y + line_height + 0.1
    #                 )  # Ã¥Å“Â¨Ã¥ÂÅ’Ã¤Â¸â‚¬Ã¨Â¡Å’Ã¯Â¼Å’Ã¤Â¸â€Ã¦Å“â€°Ã¥Å¾â€šÃ§â€ºÂ´Ã©â€¡ÂÃ¥ÂÂ 
    #                 and not last_unit.mixed_character_blacklist  # Ã¤Â¸ÂÃ¦ËœÂ¯Ã¦Â·Â·Ã¦Å½â€™Ã§Â©ÂºÃ¦Â Â¼Ã©Â»â€˜Ã¥ÂÂÃ¥Ââ€¢Ã¥Â­â€”Ã§Â¬Â¦
    #                 and not unit.mixed_character_blacklist  # Ã¥ÂÅ’Ã¤Â¸Å 
    #                 and current_x > box.x  # Ã¤Â¸ÂÃ¦ËœÂ¯Ã¨Â¡Å’Ã©Â¦â€“
    #                 and unit.try_get_unicode() != " "  # Ã¤Â¸ÂÃ¦ËœÂ¯Ã§Â©ÂºÃ¦Â Â¼
    #                 and last_unit.try_get_unicode() != " "  # Ã¤Â¸ÂÃ¦ËœÂ¯Ã§Â©ÂºÃ¦Â Â¼
    #                 and last_unit.try_get_unicode()
    #                 not in [
    #                     "Ã£â‚¬â€š",
    #                     "Ã¯Â¼Â",
    #                     "Ã¯Â¼Å¸",
    #                     "Ã¯Â¼â€º",
    #                     "Ã¯Â¼Å¡",
    #                     "Ã¯Â¼Å’",
    #                 ]
    #             ):
    #                 current_x += space_width * 0.5
    #             if use_english_line_break:
    #                 width_before_next_break_point = self._get_width_before_next_break_point(
    #                     typesetting_units[i:], scale
    #                 )
    #             else:
    #                 width_before_next_break_point = 0

    #             # Ã¥Â¦â€šÃ¦Å¾Å“Ã¥Â½â€œÃ¥â€°ÂÃ¨Â¡Å’Ã¦â€Â¾Ã¤Â¸ÂÃ¤Â¸â€¹Ã¨Â¿â„¢Ã¤Â¸ÂªÃ¥â€¦Æ’Ã§Â´Â Ã¯Â¼Å’Ã¦ÂÂ¢Ã¨Â¡Å’
    #             if not unit.is_hung_punctuation and (
    #                 (current_x + unit_width > box.x2)
    #                 or (
    #                     use_english_line_break
    #                     and current_x + unit_width + width_before_next_break_point > box.x2
    #                 )
    #                 or (
    #                     unit.is_cannot_appear_in_line_end_punctuation
    #                     and current_x + unit_width * 2 > box.x2
    #                 )
    #             ):
    #                 # Ã¦ÂÂ¢Ã¨Â¡Å’
    #                 current_x = box.x
    #                 if not current_line_heights:
    #                     return [], False
    #                 max_height = max(current_line_heights)
    #                 mode_height = statistics.mode(current_line_heights)

    #                 current_y -= max(mode_height * line_skip, max_height * 1.05)
    #                 line_ys.append(current_y)
    #                 line_height = 0.0
    #                 current_line_heights = []  # Ã¦Â¸â€¦Ã§Â©ÂºÃ¥Â½â€œÃ¥â€°ÂÃ¨Â¡Å’Ã©Â«ËœÃ¥ÂºÂ¦Ã¥Ë†â€”Ã¨Â¡Â¨

    #                 # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¦ËœÂ¯Ã¥ÂÂ¦Ã¨Â¶â€¦Ã¥â€¡ÂºÃ¥Âºâ€¢Ã©Æ’Â¨Ã¨Â¾Â¹Ã§â€¢Å’
    #                 # if current_y - unit_height < box.y:
    #                 if current_y < box.y:
    #                     all_units_fit = False
    #                     # Ã¨Â¿â„¢Ã©â€¡Å’Ã¤Â¸ÂÃ¨Â¦Â breakÃ¯Â¼Å’Ã§Â»Â§Ã§Â»Â­Ã¦Å½â€™Ã§â€°Ë†Ã¥â€°Â©Ã¤Â½â„¢Ã¥â€ â€¦Ã¥Â®Â¹

    #                 if unit.is_space:
    #                     line_height = max(line_height, unit_height)
    #                     continue

    #             # Ã¦â€Â¾Ã§Â½Â®Ã¥Â½â€œÃ¥â€°ÂÃ¥Ââ€¢Ã¥â€¦Æ’
    #             relocated_unit = unit.relocate(current_x, current_y, scale)
    #             typeset_units.append(relocated_unit)

    #             # Ã¦Â·Â»Ã¥Å Â Ã¥Â½â€œÃ¥â€°ÂÃ¥Ââ€¢Ã¥â€¦Æ’Ã§Å¡â€žÃ©Â«ËœÃ¥ÂºÂ¦Ã¥Ë†Â°Ã¥Â½â€œÃ¥â€°ÂÃ¨Â¡Å’Ã©Â«ËœÃ¥ÂºÂ¦Ã¥Ë†â€”Ã¨Â¡Â¨
    #             if not unit.is_space:
    #                 current_line_heights.append(unit_height)

    #             prev_x = current_x
    #             # Ã¦â€ºÂ´Ã¦â€“Â° x Ã¥ÂÂÃ¦Â â€¡
    #             current_x = relocated_unit.box.x2
    #             if prev_x > current_x:
    #                 logger.warning(f"Ã¥ÂÂÃ¦Â â€¡Ã¥â€ºÅ¾Ã§Â»â€¢Ã¯Â¼ÂÃ¯Â¼ÂÃ¯Â¼ÂTypesettingUnit: {unit.box}, ")

    #             last_unit = relocated_unit

    #         # *** NEW: For Arabic, right-align each line ***
    #         if is_arabic and typeset_units:
    #             # Group units by line (Y coordinate)
    #             lines = {}
    #             for unit in typeset_units:
    #                 if unit.box and unit.box.y is not None:
    #                     line_y = round(unit.box.y, 1)
    #                     if line_y not in lines:
    #                         lines[line_y] = []
    #                     lines[line_y].append(unit)
                
    #             # Right-align each line
    #             for line_y, line_units in lines.items():
    #                 if not line_units:
    #                     continue
                    
    #                 # Find the rightmost position of this line
    #                 line_max_x = max(u.box.x2 for u in line_units if u.box and u.box.x2 is not None)
                    
    #                 # Calculate how much to shift right
    #                 shift_x = box.x2 - line_max_x
                    
    #                 # Shift all units in this line to the right
    #                 for unit in line_units:
    #                     if unit.box:
    #                         unit.box.x += shift_x
    #                         unit.box.x2 += shift_x
    #                     if unit.x is not None:
    #                         unit.x += shift_x
    #                     # Update character box if present
    #                     if unit.char and unit.char.box:
    #                         unit.char.box.x += shift_x
    #                         unit.char.box.x2 += shift_x
    #                     if unit.char and unit.char.visual_bbox and unit.char.visual_bbox.box:
    #                         unit.char.visual_bbox.box.x += shift_x
    #                         unit.char.visual_bbox.box.x2 += shift_x
    #         # Check if output language is Arabic
    #         lang_out = (self.translation_config.lang_out or "").lower()
    #         is_arabic = False
    #         if lang_out in ("en-ar", "ar", "ara", "arabic"):
    #             is_arabic = True
    #         elif "-ar" in lang_out or "->ar" in lang_out or "/ar" in lang_out:
    #             is_arabic = True
            
    #         # If Arabic, reverse the line order
    #         if is_arabic and typeset_units:
    #             # Group units by line (using Y coordinates)
    #             lines_dict = {}
    #             for unit in typeset_units:
    #                 if unit.box and unit.box.y is not None:
    #                     # Round Y coordinate to group units on the same line
    #                     line_y = round(unit.box.y, 1)
    #                     if line_y not in lines_dict:
    #                         lines_dict[line_y] = []
    #                     lines_dict[line_y].append(unit)
                
    #             # Sort lines by Y coordinate (top to bottom) and reverse
    #             sorted_line_ys = sorted(lines_dict.keys(), reverse=True)
                
    #             # Rebuild typeset_units with reversed line order
    #             reversed_typeset_units = []
    #             for line_y in reversed(sorted_line_ys):
    #                 reversed_typeset_units.extend(lines_dict[line_y])
                
    #             # Now reposition all units to swap their Y coordinates
    #             # Map old Y positions to new Y positions
    #             y_mapping = {}
    #             for i, old_y in enumerate(sorted_line_ys):
    #                 new_y = sorted_line_ys[len(sorted_line_ys) - 1 - i]
    #                 y_mapping[old_y] = new_y
                
    #             # Update Y coordinates for all units
    #             for unit in reversed_typeset_units:
    #                 if unit.box and unit.box.y is not None:
    #                     old_y = round(unit.box.y, 1)
    #                     if old_y in y_mapping:
    #                         new_y = y_mapping[old_y]
    #                         y_diff = new_y - old_y
    #                         # Update the unit's Y position
    #                         if unit.y is not None:
    #                             unit.y += y_diff
    #                         if unit.box:
    #                             unit.box.y += y_diff
    #                             unit.box.y2 += y_diff
                
    #             typeset_units = reversed_typeset_units
        
    #         return typeset_units, all_units_fit

    def create_typesetting_units(
        self,
        paragraph: il_version_1.PdfParagraph,
        fonts: dict[str, il_version_1.PdfFont],
    ) -> list[TypesettingUnit]:
        if not paragraph.pdf_paragraph_composition:
            return []
        result = []

        @cache
        def get_font(font_id: str, xobj_id: int | None):
            if xobj_id in fonts:
                font = fonts[xobj_id][font_id]
            else:
                font = fonts[font_id]
            return font

        for composition in paragraph.pdf_paragraph_composition:
            if composition is None:
                continue
            if composition.pdf_line:
                result.extend(
                    [
                        TypesettingUnit(char=char)
                        for char in composition.pdf_line.pdf_character
                    ],
                )
            elif composition.pdf_character:
                result.append(
                    TypesettingUnit(
                        char=composition.pdf_character,
                        debug_info=paragraph.debug_info,
                    ),
                )
            elif composition.pdf_same_style_characters:
                result.extend(
                    [
                        TypesettingUnit(char=char)
                        for char in composition.pdf_same_style_characters.pdf_character
                    ],
                )
            elif composition.pdf_same_style_unicode_characters:
                style = composition.pdf_same_style_unicode_characters.pdf_style
                if style is None:
                    logger.warning(
                        f"Style is None. "
                        f"Composition: {composition}. "
                        f"Paragraph: {paragraph}. ",
                    )
                    continue
                font_id = style.font_id
                if font_id is None:
                    logger.warning(
                        f"Font ID is None. "
                        f"Composition: {composition}. "
                        f"Paragraph: {paragraph}. ",
                    )
                    continue
                font = get_font(font_id, paragraph.xobj_id)
                if composition.pdf_same_style_unicode_characters.unicode:
                    unicode_text = composition.pdf_same_style_unicode_characters.unicode
                    shaped_text = self.shape_arabic_text(unicode_text)
                    result.extend(
                        [
                            TypesettingUnit(
                                unicode=char_unicode,
                                font=self.font_mapper.map(
                                    font,
                                    char_unicode,
                                ),
                                original_font=font,
                                font_size=style.font_size,
                                style=style,
                                xobj_id=paragraph.xobj_id,
                                debug_info=composition.pdf_same_style_unicode_characters.debug_info
                                or False,
                            )
                            for char_unicode in shaped_text  # Use shaped_text instead of original
                            if char_unicode not in ("\n",)
                        ],
                    )
            elif composition.pdf_formula:
                result.extend([TypesettingUnit(formular=composition.pdf_formula)])
            else:
                logger.error(
                    f"Unknown composition type. "
                    f"Composition: {composition}. "
                    f"Paragraph: {paragraph}. ",
                )
                continue
        result = list(
            filter(
                lambda x: x.unicode is None or x.font is not None,
                result,
            ),
        )

        if any(x.width < 0 for x in result):
            logger.warning("Ã¦Å“â€°Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Â®Â½Ã¥ÂºÂ¦Ã¥Â°ÂÃ¤ÂºÅ½ 0Ã¯Â¼Å’Ã¨Â¯Â·Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¥Â­â€”Ã¤Â½â€œÃ¦ËœÂ Ã¥Â°â€žÃ¦ËœÂ¯Ã¥ÂÂ¦Ã¦Â­Â£Ã§Â¡Â®Ã£â‚¬â€š")
        return result

    def create_passthrough_composition(
        self,
        typesetting_units: list[TypesettingUnit],
    ) -> list[PdfParagraphComposition]:
        """Ã¤Â»Å½Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€ºÃ¥Â»ÂºÃ§â€ºÂ´Ã¦Å½Â¥Ã¤Â¼Â Ã©â‚¬â€™Ã§Å¡â€žÃ¦Â®ÂµÃ¨ÂÂ½Ã§Â»â€žÃ¥ÂË†Ã£â‚¬â€š

        Args:
            typesetting_units: Ã¦Å½â€™Ã§â€°Ë†Ã¥Ââ€¢Ã¥â€¦Æ’Ã¥Ë†â€”Ã¨Â¡Â¨

        Returns:
            Ã¦Â®ÂµÃ¨ÂÂ½Ã§Â»â€žÃ¥ÂË†Ã¥Ë†â€”Ã¨Â¡Â¨
        """
        composition = []
        for unit in typesetting_units:
            if unit.formular:
                # Ã¥Â¯Â¹Ã¤ÂºÅ½Ã¥â€¦Â¬Ã¥Â¼ÂÃ¥Ââ€¢Ã¥â€¦Æ’Ã¯Â¼Å’Ã§â€ºÂ´Ã¦Å½Â¥Ã¥Ë†â€ºÃ¥Â»ÂºÃ¥Å’â€¦Ã¥ÂÂ«Ã¥Â®Å’Ã¦â€¢Â´Ã¥â€¦Â¬Ã¥Â¼ÂÃ§Å¡â€žÃ§Â»â€žÃ¥ÂË†
                composition.append(PdfParagraphComposition(pdf_formula=unit.formular))
            else:
                # Ã¥Â¯Â¹Ã¤ÂºÅ½Ã¥Â­â€”Ã§Â¬Â¦Ã¥Ââ€¢Ã¥â€¦Æ’Ã¯Â¼Å’Ã¤Â½Â¿Ã§â€Â¨Ã¥Å½Å¸Ã¦Å“â€°Ã©â‚¬Â»Ã¨Â¾â€˜
                chars, curves, forms = unit.passthrough()
                composition.extend(
                    [PdfParagraphComposition(pdf_character=char) for char in chars],
                )
        return composition

    def get_max_right_space(self, current_box: Box, page) -> float:
        """Ã¨Å½Â·Ã¥Ââ€“Ã¦Â®ÂµÃ¨ÂÂ½Ã¥ÂÂ³Ã¤Â¾Â§Ã¦Å“â‚¬Ã¥Â¤Â§Ã¥ÂÂ¯Ã§â€Â¨Ã§Â©ÂºÃ©â€”Â´

        Args:
            current_box: Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¨Â¾Â¹Ã§â€¢Å’Ã¦Â¡â€ 
            page: Ã¥Â½â€œÃ¥â€°ÂÃ©Â¡ÂµÃ©ÂÂ¢

        Returns:
            Ã¥ÂÂ¯Ã¤Â»Â¥Ã¦â€°Â©Ã¥Â±â€¢Ã¥Ë†Â°Ã§Å¡â€žÃ¦Å“â‚¬Ã¥Â¤Â§ x Ã¥ÂÂÃ¦Â â€¡
        """
        # Ã¨Å½Â·Ã¥Ââ€“Ã©Â¡ÂµÃ©ÂÂ¢Ã§Å¡â€žÃ¨Â£ÂÃ¥â€°ÂªÃ¦Â¡â€ Ã¤Â½Å“Ã¤Â¸ÂºÃ¥Ë†ÂÃ¥Â§â€¹Ã¦Å“â‚¬Ã¥Â¤Â§Ã©â„¢ÂÃ¥Ë†Â¶
        max_x = page.cropbox.box.x2 * 0.9

        # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¦â€°â‚¬Ã¦Å“â€°Ã¥ÂÂ¯Ã¨Æ’Â½Ã§Å¡â€žÃ©ËœÂ»Ã¦Å’Â¡Ã¥â€¦Æ’Ã§Â´Â 
        for para in page.pdf_paragraph:
            if para.box == current_box or para.box is None:  # Ã¨Â·Â³Ã¨Â¿â€¡Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½
                continue
            # Ã¥ÂÂªÃ¨â‚¬Æ’Ã¨â„¢â€˜Ã¥Å“Â¨Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½Ã¥ÂÂ³Ã¤Â¾Â§Ã¤Â¸â€Ã¦Å“â€°Ã¥Å¾â€šÃ§â€ºÂ´Ã©â€¡ÂÃ¥ÂÂ Ã§Å¡â€žÃ¥â€¦Æ’Ã§Â´Â 
            if para.box.x > current_box.x and not (
                para.box.y >= current_box.y2 or para.box.y2 <= current_box.y
            ):
                max_x = min(max_x, para.box.x)
        for char in page.pdf_character:
            if char.box.x > current_box.x and not (
                char.box.y >= current_box.y2 or char.box.y2 <= current_box.y
            ):
                max_x = min(max_x, char.box.x)
        # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¥â€ºÂ¾Ã¥Â½Â¢
        for figure in page.pdf_figure:
            if figure.box.x > current_box.x and not (
                figure.box.y >= current_box.y2 or figure.box.y2 <= current_box.y
            ):
                max_x = min(max_x, figure.box.x)

        return max_x

    def get_max_bottom_space(self, current_box: Box, page: il_version_1.Page) -> float:
        """Ã¨Å½Â·Ã¥Ââ€“Ã¦Â®ÂµÃ¨ÂÂ½Ã¤Â¸â€¹Ã¦â€“Â¹Ã¦Å“â‚¬Ã¥Â¤Â§Ã¥ÂÂ¯Ã§â€Â¨Ã§Â©ÂºÃ©â€”Â´

        Args:
            current_box: Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¨Â¾Â¹Ã§â€¢Å’Ã¦Â¡â€ 
            page: Ã¥Â½â€œÃ¥â€°ÂÃ©Â¡ÂµÃ©ÂÂ¢

        Returns:
            Ã¥ÂÂ¯Ã¤Â»Â¥Ã¦â€°Â©Ã¥Â±â€¢Ã¥Ë†Â°Ã§Å¡â€žÃ¦Å“â‚¬Ã¥Â°Â y Ã¥ÂÂÃ¦Â â€¡
        """
        # Ã¨Å½Â·Ã¥Ââ€“Ã©Â¡ÂµÃ©ÂÂ¢Ã§Å¡â€žÃ¨Â£ÂÃ¥â€°ÂªÃ¦Â¡â€ Ã¤Â½Å“Ã¤Â¸ÂºÃ¥Ë†ÂÃ¥Â§â€¹Ã¦Å“â‚¬Ã¥Â°ÂÃ©â„¢ÂÃ¥Ë†Â¶
        min_y = page.cropbox.box.y * 1.1

        # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¦â€°â‚¬Ã¦Å“â€°Ã¥ÂÂ¯Ã¨Æ’Â½Ã§Å¡â€žÃ©ËœÂ»Ã¦Å’Â¡Ã¥â€¦Æ’Ã§Â´Â 
        for para in page.pdf_paragraph:
            if para.box == current_box or para.box is None:  # Ã¨Â·Â³Ã¨Â¿â€¡Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½
                continue
            # Ã¥ÂÂªÃ¨â‚¬Æ’Ã¨â„¢â€˜Ã¥Å“Â¨Ã¥Â½â€œÃ¥â€°ÂÃ¦Â®ÂµÃ¨ÂÂ½Ã¤Â¸â€¹Ã¦â€“Â¹Ã¤Â¸â€Ã¦Å“â€°Ã¦Â°Â´Ã¥Â¹Â³Ã©â€¡ÂÃ¥ÂÂ Ã§Å¡â€žÃ¥â€¦Æ’Ã§Â´Â 
            if para.box.y2 < current_box.y and not (
                para.box.x >= current_box.x2 or para.box.x2 <= current_box.x
            ):
                min_y = max(min_y, para.box.y2)
        for char in page.pdf_character:
            if char.box.y2 < current_box.y and not (
                char.box.x >= current_box.x2 or char.box.x2 <= current_box.x
            ):
                min_y = max(min_y, char.box.y2)
        # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¥â€ºÂ¾Ã¥Â½Â¢
        for figure in page.pdf_figure:
            if figure.box.y2 < current_box.y and not (
                figure.box.x >= current_box.x2 or figure.box.x2 <= current_box.x
            ):
                min_y = max(min_y, figure.box.y2)

        return min_y

    def _update_paragraph_render_order(self, paragraph: il_version_1.PdfParagraph):
        """
        Ã©â€¡ÂÃ¦â€“Â°Ã¨Â®Â¾Ã§Â½Â®Ã¦Â®ÂµÃ¨ÂÂ½Ã¥Ââ€žÃ¥Â­â€”Ã§Â¬Â¦Ã§Å¡â€ž render order
        Ã¤Â¸Â» render order Ã§Â­â€°Ã¤ÂºÅ½ paragraph Ã§Å¡â€ž renderorderÃ¯Â¼Å’sub render order Ã¤Â»Å½ 1 Ã¥Â¼â‚¬Ã¥Â§â€¹Ã¨â€¡ÂªÃ¥Â¢Å¾
        """
        if not hasattr(paragraph, "render_order") or paragraph.render_order is None:
            return

        main_render_order = paragraph.render_order
        sub_render_order = 1

        # Ã©ÂÂÃ¥Å½â€ Ã¦Â®ÂµÃ¨ÂÂ½Ã§Å¡â€žÃ¦â€°â‚¬Ã¦Å“â€°Ã§Â»â€žÃ¦Ë†ÂÃ©Æ’Â¨Ã¥Ë†â€ 
        for composition in paragraph.pdf_paragraph_composition:
            # Ã¦Â£â‚¬Ã¦Å¸Â¥Ã¥Ââ€¢Ã¤Â¸ÂªÃ¥Â­â€”Ã§Â¬Â¦
            if composition.pdf_character:
                char = composition.pdf_character
                char.render_order = main_render_order
                char.sub_render_order = sub_render_order
                sub_render_order += 1