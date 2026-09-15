#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""Regenerate the data-driven sections of note-1061-M5.html from the recorded JSON.

Replaces the region between <!--LADDER--> and <!--/LADDER--> (sec 8, the memory ladder)
and between <!--VERIFY--> and <!--/VERIFY--> (sec 11, the check table).  Idempotent:
running it twice gives the same file.
"""
import json, re, sys
import mpmath as mp
from m0_engine import Alpha
import m5_bernoulli as B

NOTE = '../note-1061-M5.html'
mp.mp.dps = 30
POLY = {'X^2-2X-1': [1, -2, -1], 'X^2-3X+1': [1, -3, 1], 'X^2-4X+1': [1, -4, 1],
        'X^3-4X^2-3X-1': [1, -4, -3, -1], 'X^3-6X^2+3X-1': [1, -6, 3, -1]}


def ladder():
    try:
        rows = json.load(open('m5_memory.json'))
    except FileNotFoundError:
        return '<p class="small">(m5_memory.json absent)</p>'
    ks = sorted({int(k) for r in rows for k in r['ladder']})
    out = ['<table>', '<tr><th>min. poly</th><th>\\(\\alpha\\)</th>'
           + ''.join('<th>\\(\\Psi_%d\\) &nbsp;\\((h(\\mu))\\)</th>' % k for k in ks)
           + '<th>\\(h_{\\min}(\\alpha)\\)</th></tr>']
    for r in rows:
        al = Alpha(POLY[r['poly']], r['poly'])
        hm = float(B.h_min(al)) if abs(al.coeffs[-1]) == 1 else None
        cells = ''
        for k in ks:
            d = r['ladder'].get(str(k))
            if d is None:
                cells += '<td>&mdash;</td>'; continue
            ent = d.get('entropy')
            below = hm is not None and ent is not None and ent < hm
            cells += '<td>%.4f%s</td>' % (
                d['Psi'], ('' if ent is None else
                           ((' <b>(%.3f)</b>' if below else ' (%.3f)') % ent)))
        out.append('<tr><td>\\(%s\\)</td><td>%.5f</td>%s<td>%s</td></tr>'
                   % (r['poly'], r['alpha'], cells, ('%.4f' % hm) if hm else 'non-unit'))
    out.append('</table>')
    out.append('<p class="small">Best value found by multi-start Nelder&ndash;Mead over the '
               '\\(2^k\\) free parameters at \\(H=12\\), then one restart from the lifted '
               '\\((k-1)\\)-optimum to enforce the monotonicity that the embedding '
               'guarantees (<code>m5_run_polish.py</code>); \\(\\Psi_1\\) at \\(1+\\sqrt2\\) is '
               'attained at Bernoulli\\((\\tfrac12)\\) itself. In brackets, the entropy of the '
               'minimising chain; <b>bold</b> marks the chains M3&rsquo;s floor already excludes.</p>')
    return '\n'.join(out)


def verify():
    rows = json.load(open('m5_verify.json'))
    out = ['<table>', '<tr><th>id</th><th>checks</th><th>result</th></tr>']
    for r in rows:
        out.append('<tr><td><code>%s</code></td><td>%s</td><td>%s &mdash; %s</td></tr>'
                   % (r['id'], r['statement'].replace('<', '&lt;').replace('>', '&gt;'),
                      '<b>PASS</b>' if r['ok'] else '<b>FAIL</b>',
                      r['detail'].replace('<', '&lt;').replace('>', '&gt;')))
    out.append('</table>')
    out.append('<p class="small">%d/%d PASS.</p>'
               % (sum(1 for r in rows if r['ok']), len(rows)))
    return '\n'.join(out)


def wide():
    try:
        rows = json.load(open('m5_wide.json'))
    except FileNotFoundError:
        return '<p class="small">(m5_wide.json absent)</p>'
    ks = sorted({int(k) for r in rows for k in r['ladder']})
    out = ['<table>', '<tr><th>min. poly</th><th>\\(h_{\\min}\\)</th>'
           + ''.join('<th>\\(\\Psi_%d\\) audited</th>' % k for k in ks)
           + '<th>naive \\(\\Psi_1\\to\\Psi_%d\\)</th><th>audited</th></tr>' % ks[-1]]
    for r in rows:
        cells, first, last = '', None, None
        for k in ks:
            d = r['ladder'].get(str(k))
            if d is None:
                cells += '<td>&mdash;</td>'; continue
            v = d['Psi_wide_ent']
            binds = d['Psi_wide_ent'] > d['Psi_wide'] * (1 + 1e-6)
            cells += '<td>%.4f%s</td>' % (v, '*' if binds else '')
            if first is None: first = d
            last = d
        out.append('<tr><td>\\(%s\\)</td><td>%.4f</td>%s<td>%.2f&times;</td><td>%.2f&times;</td></tr>'
                   % (r['poly'], r['h_min'], cells,
                      first['Psi12'] / last['Psi12'],
                      first['Psi_wide_ent'] / last['Psi_wide_ent']))
    out.append('</table>')
    out.append('<p class="small">\\(\\Psi_k\\) re-minimised against \\(h\\le32\\) and subject to '
               '\\(h(\\mu)\\ge h_{\\min}(\\alpha)\\) (penalty form), from four starts including the '
               '\\(H=12\\) optimum; <code>*</code> marks the cells where the entropy constraint '
               'actually binds. Last two columns: the total drop \\(\\Psi_1\\to\\Psi_4\\) before and '
               'after the audits. No lift-polish was applied here, so the small '
               'non-monotonicities are the resolution of the search.</p>')
    return '\n'.join(out)


def splice(src, tag, body):
    pat = re.compile('<!--%s-->.*?(<!--/%s-->|$)' % (tag, tag), re.S)
    m = pat.search(src)
    if not m:
        raise SystemExit('marker %s not found' % tag)
    return src[:m.start()] + '<!--%s-->\n%s\n<!--/%s-->' % (tag, body, tag) + src[m.end():]


s = open(NOTE).read()
s = splice(s, 'LADDER', ladder())
s = splice(s, 'WIDE', wide())
s = splice(s, 'VERIFY', verify())
open(NOTE, 'w').write(s)
print('spliced LADDER, WIDE and VERIFY into', NOTE)
