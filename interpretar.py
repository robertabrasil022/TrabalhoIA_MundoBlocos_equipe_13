#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
interpretar.py -- traduz a saida numerica do miniSAT em um plano legivel.

O miniSAT so devolve inteiros (IDs de variaveis verdadeiras). A traducao
"inteiro -> simbolo" vem do arquivo .map gerado por bw2cnf_var.py.
Sem o .map a saida do solver nao tem significado (Regra de Ouro, Secao 7.4).

Passos:
  1. le o mapa (ID -> simbolo)
  2. filtra os literais positivos
  3. reune as acoes mv(b,y,p,t), ordena por t e traduz para portugues
  4. (--verbose) reconstroi o estado em cada t e deriva a relacao 'on'

Uso:
    python3 interpretar.py situacao3/resultado3.txt [--map situacao3/trab01_blocos2SAT.map] [--verbose]
(sem --map, usa o trab01_blocos2SAT.map da mesma pasta do resultado)
"""
import argparse
import os
import re
import sys

BLOCKS = {'a': 1, 'b': 1, 'c': 2, 'd': 3}
TABLE = 'T'

RE_MV = re.compile(r'^mv\((\w),(\w),(\d+),(\d+)\)$')
RE_AT = re.compile(r'^at\((\w),(\d+),(\d+)\)$')
RE_LEV = re.compile(r'^lev\((\w),(\d+),(\d+)\)$')


def ler_mapa(caminho):
    mapa = {}
    with open(caminho) as f:
        for linha in f:
            linha = linha.strip()
            if not linha:
                continue
            idx, nome = linha.split(None, 1)
            mapa[int(idx)] = nome
    return mapa


def ler_resultado(caminho):
    """Retorna (satisfiavel, conjunto de IDs verdadeiros)."""
    with open(caminho) as f:
        linhas = [l.strip() for l in f if l.strip()]
    if not linhas:
        raise SystemExit('Arquivo de resultado vazio.')
    if linhas[0].upper().startswith('UNSAT'):
        return False, set()
    if not linhas[0].upper().startswith('SAT'):
        raise SystemExit(f'Formato inesperado na 1a linha: {linhas[0]!r}')
    ids = set()
    for linha in linhas[1:]:
        for tok in linha.split():
            n = int(tok)
            if n > 0:
                ids.add(n)
    return True, ids


def spans_overlap(b1, p1, b2, p2):
    return p1 < p2 + BLOCKS[b2] and p2 < p1 + BLOCKS[b1]


def derivar_on(estado):
    """
    estado: {bloco: (p, l)}. Retorna {bloco: [apoios]} (apoio = bloco ou 'T').
    on(b,y) <-> lev(b)=l, lev(y)=l-1 e os spans se sobrepoem (ponte: varios apoios).
    """
    on = {}
    for b, (p, l) in estado.items():
        if l == 0:
            on[b] = [TABLE]
        else:
            on[b] = sorted(y for y, (q, m) in estado.items()
                           if y != b and m == l - 1 and spans_overlap(b, p, y, q))
    return on


def estados_por_tempo(mapa, verdadeiros):
    at, lev = {}, {}
    for v in verdadeiros:
        nome = mapa.get(v, '')
        m = RE_AT.match(nome)
        if m:
            at[(m.group(1), int(m.group(3)))] = int(m.group(2))
            continue
        m = RE_LEV.match(nome)
        if m:
            lev[(m.group(1), int(m.group(3)))] = int(m.group(2))
    ts = sorted({t for (_, t) in at})
    return {t: {b: (at[(b, t)], lev[(b, t)]) for b in BLOCKS if (b, t) in at and (b, t) in lev}
            for t in ts}


def acoes(mapa, verdadeiros):
    plano = []
    for v in verdadeiros:
        m = RE_MV.match(mapa.get(v, ''))
        if m:
            plano.append((int(m.group(4)), m.group(1), m.group(2), int(m.group(3))))
    return sorted(plano)


def frase(b, y, p):
    if y == TABLE:
        return f"mover bloco '{b}' para a MESA em p={p}"
    return f"mover bloco '{b}' para CIMA de '{y}' em p={p}"


def imprimir_estado(estado, titulo):
    print(titulo)
    for b in sorted(estado):
        p, l = estado[b]
        print(f'  {b}: ponto inicial p={p}, nivel l={l}')


def imprimir_on(estado, t):
    print(f"RELACOES 'on' em t={t}:")
    for b, apoios in sorted(derivar_on(estado).items()):
        if apoios == [TABLE]:
            print(f'  {b} esta na MESA')
        elif len(apoios) > 1:
            print(f"  {b} esta sobre: {', '.join(apoios)} (ponte)")
        elif apoios:
            print(f'  {b} esta sobre: {apoios[0]}')
        else:
            print(f'  {b} esta sem apoio (!)')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('resultado', help='saida do minisat (resultadoN.txt)')
    ap.add_argument('--map', default=None,
                    help='arquivo .map (padrao: trab01_blocos2SAT.map na mesma pasta do resultado)')
    ap.add_argument('--verbose', action='store_true', help='mostra estado final e relacoes on')
    a = ap.parse_args()

    if a.map is None:
        a.map = os.path.join(os.path.dirname(os.path.abspath(a.resultado)), 'trab01_blocos2SAT.map')
    mapa = ler_mapa(a.map)
    sat, verdadeiros = ler_resultado(a.resultado)
    if not sat:
        print('UNSATISFIABLE: nao existe plano com esse horizonte.')
        return 1

    plano = acoes(mapa, verdadeiros)
    print(f'PLANO ENCONTRADO ({len(plano)} acoes):')
    for i, (t, b, y, p) in enumerate(plano, 1):
        print(f'{i}. t={t}: {frase(b, y, p)}')

    if a.verbose:
        estados = estados_por_tempo(mapa, verdadeiros)
        tf = max(estados)
        print()
        imprimir_estado(estados[tf], f'ESTADO FINAL (t={tf}):')
        print()
        imprimir_on(estados[tf], tf)
        print()
        print('EVOLUCAO DO ESTADO:')
        for t in sorted(estados):
            desc = ', '.join(f'{b}=({p},{l})' for b, (p, l) in sorted(estados[t].items()))
            print(f'  t={t}: {desc}')
    return 0


if __name__ == '__main__':
    sys.exit(main())