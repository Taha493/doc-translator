import logging
import unicodedata
from functools import lru_cache
from arabic_reshaper import ArabicReshaper
from bidi.algorithm import get_display
logger = logging.getLogger(__name__)

class ArabicTextShaper:
    """Singleton class to handle Arabic text shaping consistently"""
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super(ArabicTextShaper, cls).__new__(cls)
            cls._instance._initialize()
        return cls._instance

    def _initialize(self):
        """Initialize reshaper with optimal configuration"""
        self.configuration = {
            'delete_harakat': False,
            'support_ligatures': True,
            'RIAL SIGN': True,
            # Use contextual forms instead of leaving isolated shapes
            'use_unshaped_instead_of_isolated': False,
            'shapes_file': ''
        }
        self.reshaper = ArabicReshaper(configuration=self.configuration)

    @lru_cache(maxsize=1024)
    def shape_text(self, text: str) -> str:
        """Shape Arabic text with caching to ensure consistency"""
        if not text:
            return text
        
        # Ensure text is a string
        if not isinstance(text, str):
            logger.warning("Non-string text passed to Arabic shaper: %s", type(text))
            return str(text) if text is not None else ""
        
        try:
            # Only reshape if text contains Arabic characters
            if any('\u0600' <= c <= '\u06FF' for c in text) or any('\uFB50' <= c <= '\uFDFF' for c in text):
                # Normalize to remove Arabic Presentation Forms and compatibility glyphs
                # Some translators emit contextual forms directly (U+FB50–U+FDFF, U+FE70–U+FEFF)
                # causing inconsistent rendering; normalize back to base code points first.
                normalized = unicodedata.normalize('NFKC', text)
                reshaped = self.reshaper.reshape(normalized)
                # Force right-to-left paragraph base direction for Arabic
                bidi_text = get_display(reshaped, base_dir='R')
                return bidi_text
            return text
        except Exception as e:
            logger.warning(
                "Arabic shaping failed for text: %s, error: %s",
                repr(text), str(e)
            )
            # Return original text if shaping fails
            return text

# Create singleton instance
_shaper = ArabicTextShaper()

def shape_arabic(text: str) -> str:
    """Return display-ready Arabic text using reshaping + bidi reordering."""
    return _shaper.shape_text(text)


def is_arabic_language_code(lang_code: str) -> bool:
    """Check if the language code represents Arabic.
    
    Supports various formats: 'ar', 'AR', 'en-ar', 'EN-AR', etc.
    
    Args:
        lang_code: The language code to check
        
    Returns:
        True if the language code represents Arabic, False otherwise
    """
    if not lang_code:
        return False
    
    lang_code = lang_code.lower()
    return lang_code == 'ar' or lang_code.startswith('ar-') or lang_code.endswith('-ar')

def print_arabic_shaping_comparison(text: str, lang_code: str = "en-ar") -> None:
    """Print a detailed comparison of Arabic text before and after shaping.
    
    This function is useful for debugging Arabic text rendering issues by showing:
    1. The raw text representation (with Unicode code points)
    2. The shaped text representation
    3. Visual comparison of both texts
    
    Args:
        text: The Arabic text to shape and display
        lang_code: Language code (default "en-ar" for Arabic)
    """
    if not text or not is_arabic_language_code(lang_code):
        print(f"Not Arabic text or empty: {repr(text)}")
        return
    
    try:
        import arabic_reshaper  # type: ignore
        from bidi.algorithm import get_display  # type: ignore
        
        # Apply shaping
        # if not is_arabic_shaped(text):
        shaped_text = arabic_reshaper.reshape(text)
        shaped_text = get_display(shaped_text, base_dir='R')
        # else:
        #     shaped_text = text
        
        # Print detailed comparison
        print("\n===== ARABIC TEXT SHAPING COMPARISON =====")
        print(f"Original Text:     {text}")
        print(f"Original (repr):   {repr(text)}")
        print(f"Shaped Text:       {shaped_text}")
        print(f"Shaped (repr):     {repr(shaped_text)}")
        
        # Print character-by-character comparison for detailed analysis
        # print("\nCharacter-by-Character Analysis:")
        # print("Original:  ", end="")
        # for char in text:
        #     print(f"{char}[U+{ord(char):04X}] ", end="")
        # print("\nShaped:    ", end="")
        # for char in shaped_text:
        #     print(f"{char}[U+{ord(char):04X}] ", end="")
        # print("\n=========================================\n")
        
        return shaped_text
    except Exception as e:
        print(f"Error in Arabic shaping comparison: {e}")
        return text

def is_arabic_shaped(text):
    """Check if text contains shaped Arabic characters"""
    if not text:
        return False
    return any('\uFB50' <= c <= '\uFDFF' or '\uFE70' <= c <= '\uFEFF' for c in text)

def apply_arabic_shaping_to_text(text: str, lang_code: str, debug_print: bool = False) -> str:
    """Apply Arabic shaping to text if the language is Arabic."""
    if not text:
        return text
    
    try:
        if is_arabic_language_code(lang_code):
            reshaped_text = _shaper.shape_text(text)
            
            if debug_print and text.strip():
                print_arabic_shaping_comparison(text, lang_code)
            
            return reshaped_text
        return text
    except Exception as e:
        logger.warning("Arabic shaping failed: %s", e)
        return text

def apply_arabic_shaping_to_paragraph(paragraph, lang_code: str) -> None:
    """Apply Arabic shaping to a paragraph's unicode text if it's Arabic."""
    if not paragraph or not hasattr(paragraph, 'unicode') or not paragraph.unicode:
        return
    
    if is_arabic_language_code(lang_code):
        original_unicode = paragraph.unicode
        shaped_unicode = _shaper.shape_text(original_unicode)
        
        if original_unicode != shaped_unicode:
            paragraph.unicode = shaped_unicode
            print(f"PARAGRAPH SHAPING: {repr(original_unicode)} -> {repr(shaped_unicode)}")

def apply_arabic_shaping_to_composition(composition, lang_code: str) -> None:
    """Apply Arabic shaping to a composition's unicode text if it's Arabic."""
    if not composition or not hasattr(composition, 'pdf_same_style_unicode_characters'):
        return
    
    unicode_chars = composition.pdf_same_style_unicode_characters
    if not unicode_chars or not unicode_chars.unicode:
        return
    
    original_unicode = unicode_chars.unicode
    # Check if text contains Arabic characters or language code is Arabic
    if is_arabic_language_code(lang_code) or any('\u0600' <= c <= '\u06FF' for c in original_unicode):
        try:
            shaped_unicode = _shaper.shape_text(original_unicode)
            
            if original_unicode != shaped_unicode:
                unicode_chars.unicode = shaped_unicode
                print(f"COMPOSITION SHAPING: {repr(original_unicode)} -> {repr(shaped_unicode)}")
        except Exception as e:
            logger.warning("Failed to shape composition text: %s, error: %s", 
                          repr(original_unicode), str(e))


