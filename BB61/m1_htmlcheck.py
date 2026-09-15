#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""House-style validator for the note-1061-*.html companion notes.

Checks tag balance, MathJax delimiter balance (inline \\( \\) and display $$), and that
no raw < or > survives inside a math span (MathJax would swallow the rest of the page).
Usage: python3 m1_htmlcheck.py FILE...
"""
import sys, re
from html.parser import HTMLParser

VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link',
        'meta', 'param', 'source', 'track', 'wbr'}


class Check(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.stack = []
        self.errors = []

    def handle_starttag(self, tag, attrs):
        if tag not in VOID:
            self.stack.append((tag, self.getpos()))

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        if not self.stack:
            self.errors.append('line %d: stray </%s>' % (self.getpos()[0], tag))
        elif self.stack[-1][0] != tag:
            self.errors.append('line %d: </%s> closes <%s> opened at line %d'
                               % (self.getpos()[0], tag, self.stack[-1][0], self.stack[-1][1][0]))
            self.stack.pop()
        else:
            self.stack.pop()


def check(path):
    src = open(path, encoding='utf-8').read()
    p = Check()
    p.feed(src)
    errs = list(p.errors)
    if p.stack:
        errs.append('unclosed: ' + ', '.join('<%s> (line %d)' % (t, pos[0]) for t, pos in p.stack))

    body = src.split('</head>', 1)[-1]
    op, cl = body.count(r'\('), body.count(r'\)')
    if op != cl:
        errs.append('inline math: %d \\( vs %d \\)' % (op, cl))
    dd = body.count('$$')
    if dd % 2:
        errs.append('display math: odd number of $$ (%d)' % dd)

    # display via \[ ... \] only renders if the MathJax config lists that delimiter
    br = body.count(r'\[')
    if br:
        cfg = re.search(r'displayMath:\s*(\[.*?\])\s*\}', src, re.S)
        if cfg and r"'\\['" not in cfg.group(1):
            errs.append('%d \\[ display blocks but displayMath config does not list them: %s'
                        % (br, cfg.group(1)))
        if br != body.count(r'\]'):
            errs.append('display math: %d \\[ vs %d \\]' % (br, body.count(r'\]')))

    spans = (re.findall(r'\\\((.*?)\\\)', body, re.S) + re.findall(r'\$\$(.*?)\$\$', body, re.S)
             + re.findall(r'\\\[(.*?)\\\]', body, re.S))
    raw = [s for s in spans if '<' in s or '>' in s]
    for s in raw:
        errs.append('raw angle bracket inside math: %r' % s[:70])

    print('%-28s tags %s | inline %d/%d | display %d+%d | math spans %d | raw-angle %d'
          % (path, 'OK' if not p.stack and not p.errors else 'FAIL', op, cl, dd // 2,
             body.count(r'\['), len(spans), len(raw)))
    for e in errs:
        print('   !! ' + e)
    return not errs


if __name__ == '__main__':
    ok = all([check(f) for f in sys.argv[1:]])
    sys.exit(0 if ok else 1)
