"""Bundle this generator's self-contained RowN modules, preserving each body.

This is source packaging, not a certificate checker or a general Lean parser.
Row81 remains separate because it is the independently used infinite-tail base.
"""
from pathlib import Path
import argparse
import json

ROWS = tuple(range(5, 82))
PREFIX = 'Sendov.DistillationFinite.'


def split_row(text):
    lines = text.splitlines(keepends=True)
    imports = [line.rstrip('\r\n') for line in lines if line.startswith('import ')]
    if not imports or any(PREFIX in line for line in imports):
        raise ValueError('rows must import shared helpers, not one another')
    return imports, ''.join(line for line in lines if not line.startswith('import '))


def bundle(source, output, size=8):
    source, output = Path(source), Path(output)
    if not isinstance(size, int) or size < 1:
        raise ValueError('positive rows-per-module required')
    rows_dir = source / 'Sendov/DistillationFinite'
    expected = {f'Row{m}.lean' for m in ROWS}
    if {p.name for p in rows_dir.glob('Row*.lean')} != expected:
        raise ValueError('rows must be exactly Row5 through Row81')
    rows = {m: split_row((rows_dir / f'Row{m}.lean').read_text()) for m in ROWS}
    aggregate = (source / 'Sendov/Common/DistillationFinite.lean').read_text()
    row_imports = [line for line in aggregate.splitlines() if line.startswith(f'import {PREFIX}Row')]
    if row_imports != [f'import {PREFIX}Row{m}' for m in ROWS]:
        raise ValueError('aggregate must import each row exactly once in original order')
    groups = [list(range(start, min(start + size, 81))) for start in range(5, 81, size)] + [[81]]
    rendered, manifest = {}, []
    for group in groups:
        name = 'Row81' if group == [81] else f'Rows{group[0]}_{group[-1]}'
        path = f'Sendov/DistillationFinite/{name}.lean'
        if group == [81]:
            text = (rows_dir / 'Row81.lean').read_text()
        else:
            imports = list(dict.fromkeys(line for m in group for line in rows[m][0]))
            text = '\n'.join(imports) + '\n\n'
            text += '\n'.join('section\n' + rows[m][1] + '\nend\n' for m in group)
        rendered[path] = text
        manifest.append({'module': PREFIX + name, 'path': path, 'rows': group})
    replacements = ''.join(f"import {group['module']}\n" for group in manifest)
    new_aggregate, inserted = [], False
    for line in aggregate.splitlines(keepends=True):
        if line.startswith(f'import {PREFIX}Row'):
            if not inserted:
                new_aggregate.append(replacements); inserted = True
        else:
            new_aggregate.append(line)
    rendered['Sendov/Common/DistillationFinite.lean'] = ''.join(new_aggregate)
    # Complete validation/render first, and never overwrite an existing projection.
    output.mkdir(parents=True, exist_ok=False)
    for path, text in rendered.items():
        target = output / path; target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    return {'groups': manifest, 'candidate_paths': sorted(rendered), 'rows': list(ROWS),
            'source_lines': sum(len(text.splitlines()) for text in rendered.values()),
            'source_bytes': sum(len(text.encode()) for text in rendered.values()),
            'scope': 'Source bodies preserved; complete compiler/kernel acceptance still required.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--rows-per-module', type=int, default=8)
    args = parser.parse_args()
    print(json.dumps(bundle(args.source, args.output, args.rows_per_module), indent=2))
