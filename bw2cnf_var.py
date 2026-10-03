#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
bw2cnf_var.py -- Mundo dos Blocos de tamanho variavel -> CNF (DIMACS)

Segue a descricao formal do relatorio (Secoes 2 e 3):
  * variaveis base : at(b,p,t), lev(b,l,t), clr(b,t), mv(b,y,p,t)
  * variaveis aux. : cb(b,s,l,t), cov(s,l,t), pos(b,p,l,t), on(b,y,t) (ordem parcial)
  * 11 grupos de clausulas do Manual, com os ajustes da Secao 2.7:
      - sem a pre-condicao clr(y,t)                         (Secao 3.3)
      - clausula do slot sob a ponte                        (Secao 3.4)
      - efeitos completos (apoio antigo / todos os apoios)  (via grupo 7)
  * clausula de ordem parcial                               (Secao 2.6)
  * 'on' NAO e codificada: e derivada em interpretar.py.

Fluxo do Manual (Secao 6):
    1. editar CENARIO_PADRAO (ou INITIAL/GOAL/HORIZON) abaixo
    2. python3 bw2cnf_var.py                      -> gera <situacaoX>/*.cnf e *.map
    3. minisat <situacaoX>/trab01_blocos2SAT.cnf <situacaoX>/resultadoX.txt
    4. python3 interpretar.py <situacaoX>/resultadoX.txt --verbose

Uso:
    python3 bw2cnf_var.py                          # usa INITIAL/GOAL/HORIZON abaixo
    python3 bw2cnf_var.py --cenario sit3 --horizon 6
    python3 bw2cnf_var.py --cenario sit1_sf4 --horizon 4 --prefix trab01_blocos2SAT

Saida: <situacaoX>/trab01_blocos2SAT.cnf e .map  (a pasta e criada automaticamente;
       use --prefix para gravar em outro lugar)
"""
import argparse
import itertools
import math
import os
import sys

# ----------------------------------------------------------------------------
# DOMINIO
# ----------------------------------------------------------------------------
BLOCKS = {'a': 1, 'b': 1, 'c': 2, 'd': 3}   # comprimentos l(b)
MAX_POINT = 6                               # pontos 0..6 -> 6 slots
MAX_LEVEL = 3                               # niveis 0..3 (0 = mesa)
TABLE = 'T'                                 # simbolo da mesa (T = horizonte nos textos)

# ----------------------------------------------------------------------------
# CENARIOS  (ponto, nivel) por bloco
#   ordem: lista de pares (phi1, phi2) para  phi1 <_P phi2
#     ('lev', b, l)      : lev(b,l,t)
#     ('pos', b, p, l)   : at(b,p,t) ^ lev(b,l,t)
#     ('on',  b, y)      : on(b,y,t)   (so como phi2)
# ----------------------------------------------------------------------------
_S0_SIT1 = {'c': (0, 0), 'a': (3, 0), 'b': (5, 0), 'd': (3, 1)}
_ORDEM_D_ANTES_A = [(('lev', 'd', 0), ('on', 'a', 'c'))]   # d na mesa < a sobre c

CENARIOS = {
    # --- Situacao 1 ---------------------------------------------------------
    'sit1_sf1': dict(initial=_S0_SIT1, goal={'d': (3, 0), 'a': (4, 1), 'b': (5, 1), 'c': (4, 2)},
                     ordem=[], esperado=9),
    'sit1_sf2': dict(initial=_S0_SIT1, goal={'d': (3, 0), 'c': (4, 1), 'a': (4, 2), 'b': (5, 2)},
                     ordem=[], esperado=10),
    'sit1_sf3': dict(initial=_S0_SIT1, goal={'c': (0, 0), 'a': (2, 0), 'b': (5, 0), 'd': (0, 1)},
                     ordem=[], esperado=10),
    'sit1_sf4': dict(initial=_S0_SIT1, goal={'c': (0, 0), 'a': (0, 1), 'd': (2, 0), 'b': (5, 0)},
                     ordem=_ORDEM_D_ANTES_A, esperado=4),
    # --- Situacao 2 (S0 -> S5) ---------------------------------------------
    # phi1 = c em (4,1) ; phi2 = a em (4,2) ; phi3 = b em (5,2)   (a, b so depois de c)
    'sit2': dict(initial={'a': (0, 1), 'b': (1, 1), 'c': (0, 0), 'd': (3, 0)},
                 goal={'a': (4, 2), 'b': (5, 2), 'c': (4, 1), 'd': (3, 0)},
                 ordem=[(('pos', 'c', 4, 1), ('pos', 'a', 4, 2)),
                        (('pos', 'c', 4, 1), ('pos', 'b', 5, 2))],
                 esperado=5),
    # --- Situacao 3 (S0 -> S7) ---------------------------------------------
    'sit3': dict(initial=_S0_SIT1,
                 goal={'c': (0, 0), 'a': (0, 1), 'b': (1, 1), 'd': (3, 0)},
                 ordem=_ORDEM_D_ANTES_A, esperado=6),
}

# ---- Configuracao padrao (edite aqui, como no Manual, ou use --cenario) -----
# Passo 1 do Manual: escolha o cenario (ou escreva INITIAL/GOAL/HORIZON a mao).
#   sit1_sf4 -> situacao1 | sit2 -> situacao2 | sit3 -> situacao3
CENARIO_PADRAO = 'sit2'
INITIAL = CENARIOS[CENARIO_PADRAO]['initial']
GOAL = CENARIOS[CENARIO_PADRAO]['goal']
HORIZON = CENARIOS[CENARIO_PADRAO]['esperado']
ORDEM_PARCIAL = CENARIOS[CENARIO_PADRAO]['ordem']
OUT_PREFIX = 'trab01_blocos2SAT'

# Pasta de saida e nome do arquivo de resultado de cada cenario
PASTA = {'sit1_sf4': ('situacao1', 'resultado1.txt'),
         'sit2': ('situacao2', 'resultado2.txt'),
         'sit3': ('situacao3', 'resultado3.txt'),
         'sit1_sf1': ('situacao1/extras_sf1', 'resultado_sf1.txt'),
         'sit1_sf2': ('situacao1/extras_sf2', 'resultado_sf2.txt'),
         'sit1_sf3': ('situacao1/extras_sf3', 'resultado_sf3.txt')}


# ----------------------------------------------------------------------------
# FUNCOES AUXILIARES DE GEOMETRIA
# ----------------------------------------------------------------------------
def valid_positions(b):
    """Pontos iniciais validos de b: 0 <= p <= 6 - l(b)."""
    return range(MAX_POINT - BLOCKS[b] + 1)


def span(b, p):
    """Slots cobertos por b quando comeca no ponto p."""
    return range(p, p + BLOCKS[b])


def spans_overlap(b1, p1, b2, p2):
    """overlap(b1,p1,b2,p2) <-> p1 < p2+l(b2) e p2 < p1+l(b1)."""
    return p1 < p2 + BLOCKS[b2] and p2 < p1 + BLOCKS[b1]


# ----------------------------------------------------------------------------
# CODIFICACAO
# ----------------------------------------------------------------------------
def build(initial, goal, T, ordem=()):
    """
    Constroi o CNF. Retorna (nvars, clauses, names) onde names[id] = simbolo.
    T = horizonte (numero de acoes do plano).
    """
    names = {}
    clauses = []
    counter = itertools.count(1)

    def new_var(name):
        v = next(counter)
        names[v] = name
        return v

    blocks = list(BLOCKS)
    movers = blocks + [TABLE]          # possiveis y em mv(b,y,p,t)
    levels = range(MAX_LEVEL + 1)

    # ---- variaveis base ----------------------------------------------------
    at, lev, clr, mv = {}, {}, {}, {}
    for t in range(T + 1):
        for b in blocks:
            for p in valid_positions(b):
                at[(b, p, t)] = new_var(f'at({b},{p},{t})')
            for l in levels:
                lev[(b, l, t)] = new_var(f'lev({b},{l},{t})')
            clr[(b, t)] = new_var(f'clr({b},{t})')
    for t in range(T):
        for b in blocks:
            for y in movers:
                if y == b:
                    continue
                for p in valid_positions(b):
                    mv[(b, y, p, t)] = new_var(f'mv({b},{y},{p},{t})')
    n_base = len(names)

    # ---- variaveis auxiliares cb / cov (cobertura de slots) ------------------
    cb, cov = {}, {}
    for t in range(T + 1):
        for s in range(MAX_POINT):
            for l in levels:
                cov[(s, l, t)] = new_var(f'cov({s},{l},{t})')
                for b in blocks:
                    cb[(b, s, l, t)] = new_var(f'cb({b},{s},{l},{t})')

    def add(*lits):
        clauses.append(list(lits))

    # ---- definicao de cb e cov (equivalencias) -------------------------------
    for t in range(T + 1):
        for s in range(MAX_POINT):
            for l in levels:
                c = cov[(s, l, t)]
                for b in blocks:
                    x = cb[(b, s, l, t)]
                    ps = [p for p in valid_positions(b) if s in span(b, p)]
                    for p in ps:                       # at ^ lev -> cb
                        add(-at[(b, p, t)], -lev[(b, l, t)], x)
                    add(-x, lev[(b, l, t)])            # cb -> lev
                    add(-x, *[at[(b, p, t)] for p in ps])   # cb -> OU at
                    add(-x, c)                         # cb -> cov
                add(-c, *[cb[(b, s, l, t)] for b in blocks])  # cov -> OU cb

    # ---- 1. ESTADO INICIAL / 2. META -----------------------------------------
    for b, (p, l) in initial.items():
        add(at[(b, p, 0)])
        add(lev[(b, l, 0)])
    for b, (p, l) in goal.items():
        add(at[(b, p, T)])
        add(lev[(b, l, T)])

    # ---- 3. UNICIDADE DE POSICAO / 4. UNICIDADE DE NIVEL --------------------
    for t in range(T + 1):
        for b in blocks:
            ps = list(valid_positions(b))
            add(*[at[(b, p, t)] for p in ps])
            for p1, p2 in itertools.combinations(ps, 2):
                add(-at[(b, p1, t)], -at[(b, p2, t)])
            add(*[lev[(b, l, t)] for l in levels])
            for l1, l2 in itertools.combinations(levels, 2):
                add(-lev[(b, l1, t)], -lev[(b, l2, t)])

    # ---- 5. EXCLUSAO HORIZONTAL ---------------------------------------------
    for t in range(T + 1):
        for b1, b2 in itertools.combinations(blocks, 2):
            for p1 in valid_positions(b1):
                for p2 in valid_positions(b2):
                    if spans_overlap(b1, p1, b2, p2):
                        for l in levels:
                            add(-at[(b1, p1, t)], -lev[(b1, l, t)],
                                -at[(b2, p2, t)], -lev[(b2, l, t)])

    # ---- 6. ESTABILIDADE -----------------------------------------------------
    # b em (p,l>0): >= ceil(l(b)/2) slots do span cobertos no nivel l-1.
    # Uma clausula por subconjunto S do span com |S| = l(b) - ceil(l(b)/2) + 1.
    for t in range(T + 1):
        for b in blocks:
            need = math.ceil(BLOCKS[b] / 2)
            k = BLOCKS[b] - need + 1
            for p in valid_positions(b):
                for l in range(1, MAX_LEVEL + 1):
                    for S in itertools.combinations(list(span(b, p)), k):
                        add(-at[(b, p, t)], -lev[(b, l, t)],
                            *[cov[(s, l - 1, t)] for s in S])

    # ---- 7. CLEAR ------------------------------------------------------------
    for t in range(T + 1):
        for b in blocks:
            for p in valid_positions(b):
                for l in levels:
                    if l + 1 > MAX_LEVEL:               # nada pode estar acima
                        add(-at[(b, p, t)], -lev[(b, l, t)], clr[(b, t)])
                        continue
                    above = [cov[(s, l + 1, t)] for s in span(b, p)]
                    for c in above:                     # coberto -> nao livre
                        add(-at[(b, p, t)], -lev[(b, l, t)], -c, -clr[(b, t)])
                    add(-at[(b, p, t)], -lev[(b, l, t)], clr[(b, t)], *above)

    # ---- 8. PRE-CONDICOES / 9. EFEITOS de mv(b,y,p,t) -----------------------
    for t in range(T):
        for b in blocks:
            for y in movers:
                if y == b:
                    continue
                for p in valid_positions(b):
                    v = mv[(b, y, p, t)]
                    # (a) topo de b livre
                    add(-v, clr[(b, t)])
                    # (b) clr(y) NAO e exigida (Secao 3.3)
                    if y != TABLE:
                        # nivel maximo: y no nivel 3 -> destino seria o nivel 4
                        add(-v, -lev[(y, MAX_LEVEL, t)])
                    # (c) destino diferente da posicao atual
                    if y == TABLE:
                        add(-v, -at[(b, p, t)], -lev[(b, 0, t)])
                    else:
                        for m in range(MAX_LEVEL):
                            add(-v, -at[(b, p, t)], -lev[(y, m, t)], -lev[(b, m + 1, t)])
                    # (d) span de b em p sobrepoe o span de y
                    if y != TABLE:
                        for q in valid_positions(y):
                            if not spans_overlap(b, p, y, q):
                                add(-v, -at[(y, q, t)])
                    # (e) slots do nivel-alvo livres  +  3.4 slot sob a ponte
                    for x in blocks:
                        if x == b or x == y:
                            continue
                        for q in valid_positions(x):
                            if not spans_overlap(b, p, x, q):
                                continue
                            if y == TABLE:
                                add(-v, -at[(x, q, t)], -lev[(x, 0, t)])          # (e)
                                for k in range(1, MAX_LEVEL + 1):                 # 3.4
                                    add(-v, -at[(x, q, t)], -lev[(x, k, t)])
                            else:
                                for m in range(MAX_LEVEL):
                                    add(-v, -lev[(y, m, t)], -at[(x, q, t)],
                                        -lev[(x, m + 1, t)])                      # (e)
                                    for k in range(m + 2, MAX_LEVEL + 1):         # 3.4
                                        add(-v, -lev[(y, m, t)], -at[(x, q, t)],
                                            -lev[(x, k, t)])
                    # ---- efeitos ----
                    add(-v, at[(b, p, t + 1)])
                    if y == TABLE:
                        add(-v, lev[(b, 0, t + 1)])
                    else:
                        for m in range(MAX_LEVEL):
                            add(-v, -lev[(y, m, t)], lev[(b, m + 1, t + 1)])
                        add(-v, -clr[(y, t + 1)])

    # ---- 10. FRAME AXIOMS ----------------------------------------------------
    for t in range(T):
        for b in blocks:
            Mb = [mv[(b, y, p, t)] for y in movers if y != b for p in valid_positions(b)]
            for p in valid_positions(b):
                add(-at[(b, p, t)], at[(b, p, t + 1)], *Mb)
            for l in levels:
                add(-lev[(b, l, t)], lev[(b, l, t + 1)], *Mb)

    # ---- 11. ACAO UNICA POR PASSO -------------------------------------------
    for t in range(T):
        acts = [v for (b, y, p, tt), v in mv.items() if tt == t]
        add(*acts)
        for v1, v2 in itertools.combinations(acts, 2):
            add(-v1, -v2)
    # (para T = 0 nao ha acoes: o CNF e SAT sse INITIAL == GOAL)

    # ---- ORDEM PARCIAL  phi1 <_P phi2 ---------------------------------------
    aux = {}

    def phi(spec, t, antecedente):
        """Literal que representa phi(t). 'on' so serve como antecedente (phi2)."""
        kind = spec[0]
        if kind == 'lev':
            return lev[(spec[1], spec[2], t)]
        if kind == 'pos':
            key = spec
            _, b, p, l = spec
            k = (key, t)
            if k not in aux:
                A = new_var(f'pos({b},{p},{l},{t})')
                aux[k] = A
                add(-A, at[(b, p, t)])
                add(-A, lev[(b, l, t)])
                add(-at[(b, p, t)], -lev[(b, l, t)], A)
            return aux[k]
        if kind == 'on':
            _, b, y = spec
            if not antecedente:
                raise ValueError("'on' so pode ser usado como phi2 (antecedente)")
            if y == TABLE:
                return lev[(b, 0, t)]
            k = (spec, t)
            if k not in aux:
                O = new_var(f'o_on({b},{y},{t})')
                aux[k] = O
                for p in valid_positions(b):
                    for q in valid_positions(y):
                        if spans_overlap(b, p, y, q):
                            for l in range(1, MAX_LEVEL + 1):
                                add(-at[(b, p, t)], -lev[(b, l, t)],
                                    -at[(y, q, t)], -lev[(y, l - 1, t)], O)
            return aux[k]
        raise ValueError(f'especificacao de phi desconhecida: {spec}')

    for phi1, phi2 in ordem:
        for t in range(T + 1):
            # phi2(t) -> existe t' < t com phi1(t')
            add(-phi(phi2, t, True), *[phi(phi1, tp, False) for tp in range(t)])

    return len(names), clauses, names, n_base


# ----------------------------------------------------------------------------
# SAIDA
# ----------------------------------------------------------------------------
def write_files(prefix, nvars, clauses, names):
    cnf = f'{prefix}.cnf'
    mp = f'{prefix}.map'
    with open(cnf, 'w') as f:
        f.write(f'p cnf {nvars} {len(clauses)}\n')
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')
    with open(mp, 'w') as f:
        for v in sorted(names):
            f.write(f'{v} {names[v]}\n')
    return cnf, mp


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--cenario', choices=sorted(CENARIOS), help='cenario pre-definido')
    ap.add_argument('--horizon', type=int, help='horizonte T (numero de acoes)')
    ap.add_argument('--prefix', default=None,
                    help='prefixo dos arquivos (padrao: <situacaoX>/trab01_blocos2SAT)')
    ap.add_argument('--sem-ordem', action='store_true', help='desliga a clausula de ordem parcial')
    a = ap.parse_args()

    initial, goal, ordem, T = INITIAL, GOAL, ORDEM_PARCIAL, HORIZON
    if a.cenario:
        cfg = CENARIOS[a.cenario]
        initial, goal, ordem = cfg['initial'], cfg['goal'], cfg['ordem']
        T = a.horizon if a.horizon is not None else cfg['esperado']
    elif a.horizon is not None:
        T = a.horizon
    if a.sem_ordem:
        ordem = []

    nvars, clauses, names, n_base = build(initial, goal, T, ordem)
    nome = a.cenario or CENARIO_PADRAO
    prefix = a.prefix
    if prefix is None:
        pasta, res_nome = PASTA[nome]
        os.makedirs(pasta, exist_ok=True)
        prefix = os.path.join(pasta, OUT_PREFIX)
        print(f'Pasta: {pasta}/')
    cnf, mp = write_files(prefix, nvars, clauses, names)
    print(f'Gerado: {nvars} variaveis, {len(clauses)} clausulas '
          f'(base: {n_base}; auxiliares: {nvars - n_base}), horizonte T={T}')
    print(f'Arquivos: {cnf}, {mp}')
    if a.prefix is None:
        print('\nProximos passos:')
        print(f'  minisat {cnf} {pasta}/{res_nome}')
        print(f'  python3 interpretar.py {pasta}/{res_nome} --verbose')


if __name__ == '__main__':
    main()