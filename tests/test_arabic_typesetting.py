import os

from babeldoc.format.pdf.document_il import il_version_1
from babeldoc.format.pdf.translation_config import TranslationConfig
from babeldoc.format.pdf.document_il.midend.typesetting import Typesetting


def make_paragraph(text: str, font_id: str = "base"):
    style = il_version_1.PdfStyle(font_id=font_id, font_size=12, graphic_state=None)
    paragraph = il_version_1.PdfParagraph(
        first_line_indent=False,
        box=il_version_1.Box(x=100, y=100, x2=300, y2=300),
        vertical=False,
        pdf_style=style,
        pdf_paragraph_composition=[
            il_version_1.PdfParagraphComposition(
                pdf_same_style_unicode_characters=il_version_1.PdfSameStyleUnicodeCharacters(
                    unicode=text, pdf_style=style
                )
            )
        ],
        xobj_id=-1,
    )
    return paragraph


def test_arabic_shaping_and_rtl_layout_smoke(tmp_path):
    # Allow user to inject Arabic fonts for glyph coverage
    os.environ.setdefault("BABELDOC_EXTRA_FONTS", "")

    dummy_translator = object()  # placeholder, not used by Typesetting paths we touch
    cfg = TranslationConfig(
        translator=dummy_translator,  # type: ignore[arg-type]
        input_file="dummy.pdf",
        lang_in="en",
        lang_out="en-ar",
        doc_layout_model=None,
        output_dir=str(tmp_path),
    )
    typesetter = Typesetting(cfg)

    # Simple Arabic word; shaping util should not crash, and RTL should place it starting from right edge
    paragraph = make_paragraph("السلام")

    doc = il_version_1.Document(page=[il_version_1.Page(page_number=0)])
    page = doc.page[0]
    page.pdf_font = []
    page.pdf_xobject = []
    page.cropbox = il_version_1.VisualBbox(box=il_version_1.Box(0, 0, 600, 800))
    page.pdf_paragraph = [paragraph]
    page.pdf_character = []
    page.pdf_curve = []
    page.pdf_form = []
    page.pdf_rectangle = []

    typesetter.preprocess_document(doc, pbar=type("P", (), {"advance": lambda *_: None})())
    typesetter.render_page(page)

    # Ensure some output was generated
    assert any(
        comp.pdf_character for comp in paragraph.pdf_paragraph_composition if comp
    ), "Arabic paragraph did not produce any characters"

    # Mixed-direction sample with digits and parentheses; ensure characters exist
    paragraph2 = make_paragraph("بيان صحفي (14/8/2013) – Sony")
    page.pdf_paragraph = [paragraph2]
    typesetter.render_page(page)
    assert any(comp.pdf_character for comp in paragraph2.pdf_paragraph_composition if comp)

