"""Publish a fully rendered Lean file without truncating a previous target.

Modified for the round6 generator integration; Apache-2.0, see ../LICENSE.
"""
import os
from pathlib import Path
import tempfile


def write_lean(output, source):
    """Stage UTF-8/LF text beside the destination and replace only after close."""
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', newline='\n',
                                         dir=output.parent, prefix='.' + output.name + '.',
                                         suffix='.tmp', delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(source)
        os.replace(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
