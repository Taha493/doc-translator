import copy
import json
import threading
from datetime import datetime
from pathlib import Path
from typing import Any

import orjson
from xsdata.formats.dataclass.context import XmlContext
from xsdata.formats.dataclass.parsers import XmlParser
from xsdata.formats.dataclass.serializers import XmlSerializer
from xsdata.formats.dataclass.serializers.config import SerializerConfig

from babeldoc.format.pdf.document_il import il_version_1


class XMLConverter:
    def __init__(self):
        self.parser = XmlParser()
        config = SerializerConfig(indent="  ")
        context = XmlContext()
        self.serializer = XmlSerializer(context=context, config=config)

        # Internal state (not related to file paths)
        self._lock = threading.Lock()
        self.step_counter = 0
        self.current_stage = None

    # ==================== XML / JSON CONVERSION ====================

    def write_xml(self, document: il_version_1.Document, path: str):
        with Path(path).open("w", encoding="utf-8") as f:
            f.write(self.to_xml(document))

    def read_xml(self, path: str) -> il_version_1.Document:
        with Path(path).open(encoding="utf-8") as f:
            return self.from_xml(f.read())

    def to_xml(self, document: il_version_1.Document) -> str:
        return self.serializer.render(document)

    def from_xml(self, xml: str) -> il_version_1.Document:
        return self.parser.from_string(xml, il_version_1.Document)

    def deepcopy(self, document: il_version_1.Document) -> il_version_1.Document:
        return copy.deepcopy(document)

    def to_json(self, document: il_version_1.Document) -> str:
        return orjson.dumps(
            document,
            option=orjson.OPT_APPEND_NEWLINE
            | orjson.OPT_INDENT_2
            | orjson.OPT_SORT_KEYS,
        ).decode()

    def write_json(self, document: il_version_1.Document, path: str):
        with Path(path).open("w", encoding="utf-8") as f:
            f.write(self.to_json(document))

    # ==================== TXT LOGGING METHODS ====================

    def _safe_write_txt(self, path: Path, text: str):
        """Thread-safe write to text file."""
        try:
            with self._lock:
                with path.open("a", encoding="utf-8", errors="replace") as f:
                    f.write(text)
        except Exception as e:
            print(f"⚠️ Logging failed: {e}")

    def _write_txt_header(self, path: Path):
        """Write log header."""
        header = (
            "=" * 100 + "\n"
            "PDF TRANSLATION DETAILED LOG\n"
            f"Started at: {datetime.now().isoformat()}\n"
            + "=" * 100 + "\n\n"
        )
        self._safe_write_txt(path, header)

    def _write_txt_footer(self, path: Path):
        """Write log footer."""
        footer = (
            "\n" + "=" * 100 + "\n"
            f"Completed at: {datetime.now().isoformat()}\n"
            + "=" * 100 + "\n"
        )
        self._safe_write_txt(path, footer)

    def start_txt_stage(self, path: str, stage_name: str):
        """Start a new stage in logging."""
        path_obj = Path(path)
        path_obj.parent.mkdir(parents=True, exist_ok=True)

        # Start of new log — write header if file doesn't exist yet
        if not path_obj.exists() or path_obj.stat().st_size == 0:
            self._write_txt_header(path_obj)

        self.current_stage = stage_name
        self.step_counter = 0
        self._safe_write_txt(
            path_obj,
            f"\n{'=' * 100}\nSTAGE: {stage_name}\n{'=' * 100}\n\n"
        )

    def end_txt_stage(self, path: str, stage_name: str):
        """End a stage."""
        path_obj = Path(path)
        self._safe_write_txt(path_obj, f"\n--- End of {stage_name} ---\n\n")

    def log_txt_step(self, path: str, step_name: str, details: str = "", data: Any = None):
        """Log a single step."""
        path_obj = Path(path)
        self.step_counter += 1

        lines = [f"\n[Step {self.step_counter}] {step_name}\n", "-" * 80 + "\n"]

        if details:
            lines.append(f"Details: {details}\n")

        if data is not None:
            lines.append("Data:\n")
            if isinstance(data, (dict, list)):
                json_data = json.dumps(data, indent=2, ensure_ascii=False)
                truncated = json_data[:5000]
                lines.append(truncated + "\n")
                if len(json_data) > 5000:
                    lines.append("... [truncated for brevity]\n")
            else:
                text_data = str(data)
                truncated = text_data[:5000]
                lines.append(truncated + "\n")
                if len(text_data) > 5000:
                    lines.append("... [truncated for brevity]\n")

        lines.append("-" * 80 + "\n")
        self._safe_write_txt(path_obj, "".join(lines))

    def log_txt_paragraph(self, path: str, paragraph_data: dict):
        """Log paragraph information."""
        text = (
            f"\n  Paragraph:\n"
            f"    Text: {paragraph_data.get('text', '')[:200]}\n"
            f"    Layout: {paragraph_data.get('layout_label', 'N/A')}\n"
            f"    Bounding box: {paragraph_data.get('box', 'N/A')}\n"
            f"    Character count: {paragraph_data.get('char_count', 0)}\n"
        )
        self._safe_write_txt(Path(path), text)

    def finalize_txt_log(self, path: str):
        """Write footer and finalize."""
        self._write_txt_footer(Path(path))
