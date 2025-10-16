#!/usr/bin/env python
"""
Arabic Text Shaping Tool

This command-line tool allows you to test Arabic text shaping directly in the terminal.
It shows the original text, the shaped text, and a character-by-character analysis.
"""

import argparse
import sys
import os

# Add the parent directory to the path so we can import babeldoc modules
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../..')))

from babeldoc.format.pdf.document_il.utils.rtl import print_arabic_shaping_comparison, shape_arabic


def main():
    parser = argparse.ArgumentParser(description='Test Arabic text shaping in the terminal')
    parser.add_argument('text', nargs='?', help='Arabic text to shape')
    parser.add_argument('--file', '-f', help='File containing Arabic text to shape')
    parser.add_argument('--interactive', '-i', action='store_true', help='Run in interactive mode')
    
    args = parser.parse_args()
    
    if args.interactive:
        print("Arabic Text Shaping Tool - Interactive Mode")
        print("Enter Arabic text to see how it will be shaped (type 'exit' to quit):")
        
        while True:
            try:
                text = input("\nEnter Arabic text: ")
                if text.lower() == 'exit':
                    break
                if not text:
                    continue
                    
                print_arabic_shaping_comparison(text)
            except KeyboardInterrupt:
                break
            except Exception as e:
                print(f"Error: {e}")
    
    elif args.file:
        try:
            with open(args.file, 'r', encoding='utf-8') as f:
                text = f.read()
            print_arabic_shaping_comparison(text)
        except Exception as e:
            print(f"Error reading file: {e}")
    
    elif args.text:
        print_arabic_shaping_comparison(args.text)
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()