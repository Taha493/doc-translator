"""
Detailed Logger for PDF Translation Process
This module provides comprehensive logging for all intermediate steps
of the PDF translation workflow.
"""

import logging
import json
from pathlib import Path
from typing import Any, Dict, List
from datetime import datetime


class DetailedLogger:
    """Logs detailed information about each step of the PDF translation process"""
    
    def __init__(self, output_path: str = "translation_detailed_log.txt"):
        self.output_path = Path(output_path)
        self.step_counter = 0
        self.current_stage = None
        
        # Make sure the directory exists
        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        
        print(f"Creating log file at: {self.output_path.absolute()}")  # Debug print
        
        # Open the file immediately upon initialization
        try:
            self.log_file = open(self.output_path, 'w', encoding='utf-8')
            self._write_header()
            print(f"Successfully created and opened log file")  # Debug print
        except Exception as e:
            print(f"Error creating log file: {str(e)}")  # Debug print
            raise
        
    def __enter__(self):
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.log_file:
            self._write_footer()
            self.log_file.close()
            
    def close(self):
        """Manually close the logger"""
        if self.log_file:
            self._write_footer()
            self.log_file.close()
            self.log_file = None
            
    def _write_header(self):
        """Write log file header"""
        self.log_file.write("=" * 100 + "\n")
        self.log_file.write("PDF TRANSLATION DETAILED LOG\n")
        self.log_file.write(f"Started at: {datetime.now().isoformat()}\n")
        self.log_file.write("=" * 100 + "\n\n")
        self.log_file.flush()
        
    def _write_footer(self):
        """Write log file footer"""
        self.log_file.write("\n" + "=" * 100 + "\n")
        self.log_file.write(f"Completed at: {datetime.now().isoformat()}\n")
        self.log_file.write("=" * 100 + "\n")
        self.log_file.flush()
        
    def start_stage(self, stage_name: str):
        """Start a new processing stage"""
        if not self.log_file:
            return
        self.current_stage = stage_name
        self.step_counter = 0
        self.log_file.write("\n" + "=" * 100 + "\n")
        self.log_file.write(f"STAGE: {stage_name}\n")
        self.log_file.write("=" * 100 + "\n\n")
        self.log_file.flush()
        
    def end_stage(self, stage_name: str):
        """End current processing stage"""
        if not self.log_file:
            return
        self.log_file.write(f"\n--- End of {stage_name} ---\n\n")
        self.log_file.flush()
        
    def log_step(self, step_name: str, details: str = "", data: Any = None):
        """Log a processing step with details"""
        if not self.log_file:
            return
            
        self.step_counter += 1
        self.log_file.write(f"\n[Step {self.step_counter}] {step_name}\n")
        self.log_file.write("-" * 80 + "\n")
        
        if details:
            self.log_file.write(f"Details: {details}\n")
            
        if data is not None:
            self.log_file.write("Data:\n")
            if isinstance(data, (dict, list)):
                self.log_file.write(json.dumps(data, indent=2, ensure_ascii=False)[:5000] + "\n")
            else:
                self.log_file.write(str(data)[:5000] + "\n")
                
        self.log_file.write("-" * 80 + "\n")
        self.log_file.flush()
        
    def log_input_output(self, operation: str, input_data: Any, output_data: Any):
        """Log input and output of an operation"""
        if not self.log_file:
            return
            
        self.step_counter += 1
        self.log_file.write(f"\n[Step {self.step_counter}] {operation}\n")
        self.log_file.write("-" * 80 + "\n")
        
        self.log_file.write("INPUT:\n")
        if isinstance(input_data, (dict, list)):
            self.log_file.write(json.dumps(input_data, indent=2, ensure_ascii=False)[:2000] + "\n")
        else:
            self.log_file.write(str(input_data)[:2000] + "\n")
            
        self.log_file.write("\nOUTPUT:\n")
        if isinstance(output_data, (dict, list)):
            self.log_file.write(json.dumps(output_data, indent=2, ensure_ascii=False)[:2000] + "\n")
        else:
            self.log_file.write(str(output_data)[:2000] + "\n")
            
        self.log_file.write("-" * 80 + "\n")
        self.log_file.flush()
        
    def log_character_extraction(self, page_num: int, char_data: Dict):
        """Log character extraction details"""
        if not self.log_file:
            return
            
        self.log_file.write(f"\n  Character extracted on page {page_num}:\n")
        self.log_file.write(f"    Unicode: '{char_data.get('unicode', '')}'\n")
        self.log_file.write(f"    Position: ({char_data.get('x', 0):.2f}, {char_data.get('y', 0):.2f})\n")
        self.log_file.write(f"    Size: {char_data.get('width', 0):.2f} x {char_data.get('height', 0):.2f}\n")
        self.log_file.write(f"    Font: {char_data.get('font_id', 'N/A')}, Size: {char_data.get('font_size', 0):.2f}\n")
        self.log_file.flush()
        
    def log_paragraph(self, paragraph_data: Dict):
        """Log paragraph information"""
        if not self.log_file:
            return
            
        self.log_file.write(f"\n  Paragraph:\n")
        self.log_file.write(f"    Text: {paragraph_data.get('text', '')[:200]}\n")
        self.log_file.write(f"    Layout: {paragraph_data.get('layout_label', 'N/A')}\n")
        self.log_file.write(f"    Bounding box: {paragraph_data.get('box', 'N/A')}\n")
        self.log_file.write(f"    Character count: {paragraph_data.get('char_count', 0)}\n")
        self.log_file.flush()
        
    def log_translation_batch(self, batch_num: int, paragraphs: List[str], translations: List[str]):
        """Log translation batch"""
        if not self.log_file:
            return
            
        self.log_file.write(f"\n  Translation Batch {batch_num}:\n")
        self.log_file.write(f"    Paragraph count: {len(paragraphs)}\n")
        for i, (orig, trans) in enumerate(zip(paragraphs, translations)):
            self.log_file.write(f"\n    [{i+1}] Original: {orig[:150]}\n")
            self.log_file.write(f"    [{i+1}] Translated: {trans[:150]}\n")
        self.log_file.flush()
            
    def log_memory_batch(self, batch_info: str, items: List[str]):
        """Log memory management batching"""
        if not self.log_file:
            return
            
        self.log_file.write(f"\n  Memory Batch: {batch_info}\n")
        self.log_file.write(f"    Items in batch: {len(items)}\n")
        for i, item in enumerate(items[:5]):  # Show first 5 items
            self.log_file.write(f"      [{i+1}] {item[:100]}\n")
        if len(items) > 5:
            self.log_file.write(f"      ... and {len(items)-5} more items\n")
        self.log_file.flush()
    
    def log_typeset_text_block(self, page_num: int, paragraph_type: str, text: str, 
                                box_coords: Dict, scale: float = None):
        """
        Log complete text blocks (paragraphs, headings, bullet points) with their coordinates
        
        Args:
            page_num: Page number where text appears
            paragraph_type: Type of text block (e.g., 'heading', 'paragraph', 'bullet_point', 'list_item')
            text: The complete text content
            box_coords: Dictionary with box coordinates {'x': float, 'y': float, 'x2': float, 'y2': float}
            scale: Optional scaling factor applied during typesetting
        """
        if not self.log_file:
            return
        
        self.log_file.write(f"\n{'='*80}\n")
        self.log_file.write(f"TYPESET TEXT BLOCK - Page {page_num}\n")
        self.log_file.write(f"{'='*80}\n")
        self.log_file.write(f"Type: {paragraph_type}\n")
        self.log_file.write(f"Coordinates:\n")
        self.log_file.write(f"  Bottom-Left:  (x={box_coords.get('x', 0):.2f}, y={box_coords.get('y', 0):.2f})\n")
        self.log_file.write(f"  Top-Right:    (x2={box_coords.get('x2', 0):.2f}, y2={box_coords.get('y2', 0):.2f})\n")
        self.log_file.write(f"  Width:  {box_coords.get('x2', 0) - box_coords.get('x', 0):.2f}\n")
        self.log_file.write(f"  Height: {box_coords.get('y2', 0) - box_coords.get('y', 0):.2f}\n")
        if scale is not None:
            self.log_file.write(f"Scale: {scale:.4f}\n")
        self.log_file.write(f"\nText Content ({len(text)} characters):\n")
        self.log_file.write(f"{'-'*80}\n")
        self.log_file.write(f"{text}\n")
        self.log_file.write(f"{'-'*80}\n\n")
        self.log_file.flush()


# Global logger instance
_global_logger = None


def get_detailed_logger(output_path: str = None) -> DetailedLogger:
    """Get or create the global detailed logger"""
    global _global_logger
    if _global_logger is None and output_path:
        _global_logger = DetailedLogger(output_path)
    return _global_logger


def init_detailed_logger(output_path: str) -> DetailedLogger:
    """Initialize the detailed logger"""
    global _global_logger
    _global_logger = DetailedLogger(output_path)
    return _global_logger