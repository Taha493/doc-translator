#!/usr/bin/env python3
"""
Test script for Arabic text reshaping functionality.
This script verifies the fixes for inconsistent Arabic text shaping.
"""

import sys
import os

# Add the parent directory to the Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from format.pdf.document_il.utils.rtl import (
    ArabicTextShaper, 
    is_arabic_language_code,
    apply_arabic_shaping_to_text,
    print_arabic_shaping_comparison
)

def test_arabic_shaping():
    """Test Arabic text shaping with various scenarios."""
    print("Testing Arabic text shaping...")
    
    # Test with pure Arabic text
    pure_arabic = "بيان صحفي لـلولسيكوا ملخصات"
    print("\n1. Pure Arabic text:")
    shaped_pure_arabic = apply_arabic_shaping_to_text(pure_arabic, "en-ar")
    print(f"Original: {pure_arabic}")
    print(f"Shaped:   {shaped_pure_arabic}")
    
    # Test with mixed Arabic and Latin text (problematic case)
    mixed_text = "Circular no.(66/2013) dated 14/8/2013 بيان صحفي"
    print("\n2. Mixed Arabic and Latin text:")
    shaped_mixed = apply_arabic_shaping_to_text(mixed_text, "en-ar")
    print(f"Original: {mixed_text}")
    print(f"Shaped:   {shaped_mixed}")
    
    # Test with different language codes
    print("\n3. Testing different language codes:")
    lang_codes = ["en-ar", "ar", "AR", "en-AR", "ar-en"]
    test_text = "مرحبا بالعالم"
    
    for lang_code in lang_codes:
        print(f"\nLanguage code: {lang_code}")
        print(f"Is Arabic: {is_arabic_language_code(lang_code)}")
        shaped = apply_arabic_shaping_to_text(test_text, lang_code)
        print(f"Original: {test_text}")
        print(f"Shaped:   {shaped}")
    
    # Test with edge cases
    print("\n4. Edge cases:")
    edge_cases = [
        ("Empty string", ""),
        ("Numbers only", "12345"),
        ("Latin only", "Hello World"),
        ("Arabic with numbers", "رقم 12345"),
        ("Mixed with special chars", "تاريخ (14/8/2013)"),
    ]
    
    for name, text in edge_cases:
        print(f"\n{name}:")
        shaped = apply_arabic_shaping_to_text(text, "en-ar")
        print(f"Original: {text}")
        print(f"Shaped:   {shaped}")

if __name__ == "__main__":
    test_arabic_shaping()