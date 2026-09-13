"""Publication guarantees for the retained single-file sinh generator."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import generator_output


class PublicationTests(unittest.TestCase):
    def test_writer_success_replaces_target_and_cleans_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'file.lean'
            output.write_bytes(b'old')
            generator_output.write_lean(output, 'new \u03b1\n')
            self.assertEqual(output.read_bytes(), 'new \u03b1\n'.encode())
            self.assertEqual(list(Path(temporary).iterdir()), [output])

    def test_writer_rejected_source_preserves_previous_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'file.lean'
            output.write_bytes(b'old')
            with self.assertRaises(TypeError):
                generator_output.write_lean(output, object())
            self.assertEqual(output.read_bytes(), b'old')
            self.assertEqual(list(Path(temporary).iterdir()), [output])

    def test_publish_failure_preserves_previous_file_and_cleans_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'file.lean'
            output.write_bytes(b'old')
            with patch.object(generator_output.os, 'replace', side_effect=OSError('publish')):
                with self.assertRaisesRegex(OSError, 'publish'):
                    generator_output.write_lean(output, 'new\n')
            self.assertEqual(output.read_bytes(), b'old')
            self.assertEqual(list(Path(temporary).iterdir()), [output])


if __name__ == '__main__':
    unittest.main()
