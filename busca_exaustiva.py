#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
busca_exaustiva.py -- verificador independente do modelo (NAO usa SAT).

Implementa as mesmas regras do relatorio como um simulador de estados e faz BFS.
Serve para:
  * achar o comprimento MINIMO de plano de cada cenario (valida o horizonte do SAT);
  * verificar, passo a passo, se um plano produzido pelo SAT e legal.

Regras de move(b,y,p) (Secao 2.4):
  P1 b livre | P2 destino valido | P3 sobreposicao com y | P4 slots livres no nivel-alvo
  P5 folga vertical (nada acima nesses slots) | P6 estabilidade | P7 acao nao nula

Uso:
    python3 busca_exaustiva.py             # todos os cenarios
    python3 busca_exaustiva.py sit3
"""
import math
import sys
from collections import deque

from bw2cnf_var import BLOCKS, CENARIOS, MAX_LEVEL, MAX_POINT, TABLE


def span(b, p):
    return range(p, p + BLOCKS[b])


def cobertura(estado):
    c = {}
    for b, (p, l) in estado.items():
        for s in span(b, p):
            c.setdefault((s, l), []).append(b)
    return c


def livre(estado, b):
    p, l = estado[b]
    c = cobertura(estado)
    return not any((s, l + 1) in c for s in span(b, p))


def sucessores(estado):
    """Gera ((b,y,p), novo_estado) para todas as acoes legais."""
    for b in BLOCKS:
        if not livre(estado, b):                                   # P1
            continue
        resto = {k: v for k, v in estado.items() if k != b}
        c = cobertura(resto)
        for y in list(BLOCKS) + [TABLE]:
            if y == b:
                continue
            if y == TABLE:
                alvo = 0
            else:
                alvo = estado[y][1] + 1
                if alvo > MAX_LEVEL:
                    continue
            for p in range(MAX_POINT - BLOCKS[b] + 1):             # P2
                if y != TABLE:
                    q = estado[y][0]
                    if not (p < q + BLOCKS[y] and q < p + BLOCKS[b]):  # P3
                        continue
                if estado[b] == (p, alvo):                         # P7
                    continue
                sl = list(span(b, p))
                if any((s, alvo) in c for s in sl):                # P4
                    continue
                if any((s, k) in c for s in sl for k in range(alvo + 1, MAX_LEVEL + 1)):  # P5
                    continue
                if alvo > 0:                                       # P6
                    if sum(1 for s in sl if (s, alvo - 1) in c) < math.ceil(BLOCKS[b] / 2):
                        continue
                yield (b, y, p), {**resto, b: (p, alvo)}


def chave(estado):
    return tuple(sorted(estado.items()))


def plano_minimo(inicial, meta):
    fila = deque([inicial])
    prev = {chave(inicial): None}
    while fila:
        s = fila.popleft()
        if chave(s) == chave(meta):
            caminho, k = [], chave(s)
            while prev[k]:
                acao, pk = prev[k]
                caminho.append(acao)
                k = pk
            return caminho[::-1]
        for acao, n in sucessores(s):
            if chave(n) not in prev:
                prev[chave(n)] = (acao, chave(s))
                fila.append(n)
    return None


def verificar_plano(inicial, meta, plano):
    """plano: lista de (b,y,p). Retorna (ok, mensagem)."""
    s = dict(inicial)
    for i, acao in enumerate(plano):
        for a, n in sucessores(s):
            if a == acao:
                s = n
                break
        else:
            return False, f'acao {i + 1} {acao} ilegal no estado {chave(s)}'
    if chave(s) != chave(meta):
        return False, f'estado final {chave(s)} difere da meta'
    return True, 'plano legal e atinge a meta'


if __name__ == '__main__':
    nomes = sys.argv[1:] or sorted(CENARIOS)
    for nome in nomes:
        cfg = CENARIOS[nome]
        plano = plano_minimo(cfg['initial'], cfg['goal'])
        print(f"{nome}: minimo = {len(plano)} acoes (esperado {cfg['esperado']}) -> {plano}")
