"""BabelDOC FastAPI Server - Production Ready"""
import asyncio
import logging
import os
import shutil
import tempfile
from pathlib import Path
from typing import Optional

from fastapi import FastAPI, File, Form, HTTPException, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, HTMLResponse
from fastapi.staticfiles import StaticFiles

# Import BabelDOC modules
from babeldoc.format.pdf.high_level import async_translate, init
from babeldoc.format.pdf.translation_config import TranslationConfig
from babeldoc.progress_monitor import ProgressMonitor
from babeldoc.translator.translator import OpenAITranslator

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Suppress verbose logs
logging.getLogger("httpx").setLevel("CRITICAL")
logging.getLogger("openai").setLevel("CRITICAL")

# Initialize FastAPI app
app = FastAPI(
    title="BabelDOC Translation API",
    description="Intelligent PDF Translation with Layout Preservation",
    version="1.0.0"
)

# Configure CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Change in production
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Serve frontend static files
try:
    app.mount("/static", StaticFiles(directory="frontend"), name="static")
except RuntimeError:
    logger.warning("Frontend directory not found, skipping static file serving")

# Temporary directory for file processing
TEMP_DIR = Path(tempfile.gettempdir()) / "babeldoc_api"
TEMP_DIR.mkdir(exist_ok=True)

# Language code mapping
LANGUAGE_CODES = {
    'en': 'en',
    'ar': 'ar',
    'en-ar': 'en-ar',
    'es': 'es',
    'fr': 'fr',
    'de': 'de',
    'zh': 'zh',
    'ja': 'ja',
    'ko': 'ko',
    'pt': 'pt',
    'ru': 'ru',
    'it': 'it',
}

# Initialize BabelDOC on startup
@app.on_event("startup")
async def startup_event():
    """Initialize BabelDOC resources"""
    logger.info("Initializing BabelDOC...")
    try:
        init()
        logger.info("BabelDOC initialized successfully")
    except Exception as e:
        logger.error(f"Failed to initialize BabelDOC: {e}")


@app.get("/", response_class=HTMLResponse)
async def root():
    """Serve the frontend HTML"""
    try:
        with open("frontend/index.html", "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        return {
            "name": "BabelDOC API",
            "version": "1.0.0",
            "status": "running",
            "endpoints": {
                "health": "/health",
                "languages": "/languages",
                "translate": "/translate"
            }
        }


@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {
        "status": "healthy",
        "service": "babeldoc-api",
        "version": "1.0.0"
    }


@app.get("/languages")
async def get_supported_languages():
    """Get list of supported languages"""
    return {
        "supported_languages": {
            "en": "English",
            "en-ar": "Arabic",
            "es": "Spanish",
            "fr": "French",
            "de": "German",
            "zh": "Chinese",
            "ja": "Japanese",
            "ko": "Korean",
            "pt": "Portuguese",
            "ru": "Russian",
            "it": "Italian",
        },
        "count": len(LANGUAGE_CODES)
    }


@app.post("/translate")
async def translate_document(
    file: UploadFile = File(...),
    source_lang: str = Form(...),
    target_lang: str = Form(...),
    model: Optional[str] = Form("gpt-4o-mini"),
):
    """
    Translate a PDF document from source language to target language
    
    Args:
        file: PDF file to translate
        source_lang: Source language code (e.g., 'en')
        target_lang: Target language code (e.g., 'ar')
        model: OpenAI model to use (default: gpt-4o-mini)
    
    Returns:
        Translated PDF file
    """
    
    # Validate file type
    if not file.filename.lower().endswith('.pdf'):
        raise HTTPException(
            status_code=400,
            detail="Only PDF files are supported"
        )
    
    # Validate languages
    if source_lang not in LANGUAGE_CODES:
        raise HTTPException(
            status_code=400,
            detail=f"Unsupported source language: {source_lang}. Supported: {list(LANGUAGE_CODES.keys())}"
        )
    
    if target_lang not in LANGUAGE_CODES:
        raise HTTPException(
            status_code=400,
            detail=f"Unsupported target language: {target_lang}. Supported: {list(LANGUAGE_CODES.keys())}"
        )
    
    if source_lang == target_lang:
        raise HTTPException(
            status_code=400,
            detail="Source and target languages must be different"
        )
    
    # Create session directory
    session_id = f"session_{os.urandom(8).hex()}"
    session_dir = TEMP_DIR / session_id
    session_dir.mkdir(exist_ok=True)
    
    input_path = session_dir / file.filename
    output_directory = session_dir / "output"
    output_directory.mkdir(exist_ok=True)
    
    try:
        # Save uploaded file
        logger.info(f"Processing translation: {file.filename}")
        logger.info(f"Language pair: {source_lang} -> {target_lang}")
        logger.info(f"Model: {model}")
        
        with open(input_path, "wb") as buffer:
            shutil.copyfileobj(file.file, buffer)
        
        # Verify API key
        openai_api_key = os.getenv("OPENAI_API_KEY")
        if not openai_api_key:
            raise HTTPException(
                status_code=500,
                detail="OPENAI_API_KEY not configured on server"
            )
        
        # Create translator
        translator = OpenAITranslator(
            lang_in=LANGUAGE_CODES[source_lang],
            lang_out=LANGUAGE_CODES[target_lang],
            model=model,
            api_key=openai_api_key,
            ignore_cache=True
        )
        
        # Configure translation
        config = TranslationConfig(
            translator=translator,
            input_file=str(input_path),
            lang_in=LANGUAGE_CODES[source_lang],
            lang_out=LANGUAGE_CODES[target_lang],
            output_dir=str(output_directory),
            doc_layout_model="layoutv1",
            pages=None,  # Translate all pages
            skip_clean=True,  # Keep temp files for debugging
        )
        
        # Create progress monitor
        # progress_monitor = ProgressMonitor()
        
        # Perform translation asynchronously
        logger.info("Starting translation process...")
        
        result = None
        async for event in async_translate(config):
            if event["type"] == "progress_update":
                logger.debug(
                    f"Progress: {event['stage']} - "
                    f"{event['stage_current']}/{event['stage_total']} "
                    f"(Overall: {event['overall_progress']}%)"
                )
            elif event["type"] == "finish":
                result = event["translate_result"]
                logger.info("Translation completed successfully")
                break
            elif event["type"] == "error":
                error_msg = event.get("error", "Unknown error")
                logger.error(f"Translation error: {error_msg}")
                raise HTTPException(
                    status_code=500,
                    detail=f"Translation failed: {error_msg}"
                )
        
        if result is None:
            raise HTTPException(
                status_code=500,
                detail="Translation completed but no result returned"
            )
        
        # Get the output PDF path
        # BabelDOC creates output with specific naming convention
        output_pdf = None
        
        # Try to find the translated PDF
        if result.mono_pdf_path and result.mono_pdf_path.exists():
            output_pdf = result.mono_pdf_path
        elif result.no_watermark_mono_pdf_path and result.no_watermark_mono_pdf_path.exists():
            output_pdf = result.no_watermark_mono_pdf_path
        
        if not output_pdf:
            # Fallback: search for any PDF in output directory
            pdf_files = list(output_directory.glob("*.pdf"))
            if pdf_files:
                output_pdf = pdf_files[0]
        
        if not output_pdf or not output_pdf.exists():
            raise HTTPException(
                status_code=500,
                detail="Translation completed but output file not found"
            )
        
        logger.info(f"Translation successful: {output_pdf}")
        
        # Return the translated file
        output_filename = f"translated_{file.filename}"
        
        return FileResponse(
            path=str(output_pdf),
            filename=output_filename,
            media_type="application/pdf",
            headers={
                "Content-Disposition": f"attachment; filename={output_filename}"
            }
        )
    
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Translation error: {str(e)}", exc_info=True)
        raise HTTPException(
            status_code=500,
            detail=f"Translation failed: {str(e)}"
        )
    
    finally:
        # Cleanup temporary files (optional - comment out for debugging)
        try:
            if session_dir.exists():
                shutil.rmtree(session_dir)
                logger.info(f"Cleaned up session: {session_id}")
        except Exception as e:
            logger.warning(f"Failed to cleanup session {session_id}: {e}")


if __name__ == "__main__":
    import uvicorn
    
    port = int(os.getenv("PORT", 8000))
    
    logger.info(f"Starting BabelDOC API server on port {port}")
    
    uvicorn.run(
        "server:app",
        host="0.0.0.0",
        port=port,
        log_level="info",
        reload=False  # Set to True for development
    )
