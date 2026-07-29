"""
Central AI / model configuration.

Layer: foundation (leaf). Depends only on the standard library; consumed by
``engine.py`` and ``ai.py``.

All model pins and Bedrock call knobs live in one place -- ``model-config.json``
at the tool root -- instead of being scattered across the engine and AI modules.
Precedence for each value: environment variable > ``model-config.json`` >
built-in default (so CI can still override via env, and the tool still runs if the
file is missing).

Consumed by ``engine.py`` (byte caps + the model id it re-exports) and ``ai.py``
(model id, region, max tokens). To change the model, edit ``model-config.json``.
"""

import json
import os
from pathlib import Path

# Built-in fallbacks (used only if model-config.json is missing/unreadable).
_DEFAULTS = {
    "model_id": "us.anthropic.claude-opus-4-8",
    "aws_region": "us-east-1",
    "max_tokens": 1024,
    "max_diff_bytes": 40000,
    "max_file_bytes": 45000,
}

# model-config.json sits at the tool root (one level up from src/).
_SETTINGS_PATH = Path(__file__).resolve().parent.parent / "model-config.json"


def load() -> dict:
    cfg = dict(_DEFAULTS)
    try:
        loaded = json.loads(_SETTINGS_PATH.read_text(encoding="utf-8"))
        cfg.update({k: loaded[k] for k in _DEFAULTS if k in loaded})
    except (OSError, ValueError):
        pass  # keep defaults if the file is absent or malformed
    return cfg


_CFG = load()

# Environment overrides win, then the file, then the default.
MODEL_ID = os.environ.get("BEDROCK_MODEL_ID", _CFG["model_id"])
AWS_REGION = os.environ.get("AWS_REGION", _CFG["aws_region"])
MAX_TOKENS = int(os.environ.get("BEDROCK_MAX_TOKENS", _CFG["max_tokens"]))
MAX_DIFF_BYTES = int(_CFG["max_diff_bytes"])
MAX_FILE_BYTES = int(_CFG["max_file_bytes"])
