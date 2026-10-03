#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
rodar_cenarios.py -- roda cada cenario com horizonte crescente ate SATISFIABLE.

Para cada cenario e cada T = 0, 1, 2, ...:
    1. gera o CNF e o .map (bw2cnf_var.build)
    2. executa o minisat
    3. para no primeiro SATISFIABLE, interpreta o plano, verifica-o com o
       simulador independente (busca_exaustiva) e salva os artefatos

Artefatos salvos em <saida>/<pasta>/ :
    trab01_blocos2SAT.cnf, trab01_blocos2SAT.map, resultadoN.txt
O menor T satisfativel e o comprimento minimo do plano.

Uso:
    python3 rodar_cenarios.py                       # sit1_sf4, sit2, sit3
    python3 rodar_cenarios.py --todos               # inclui Sf1, Sf2, Sf3 (horizontes ate 10)
    python3 rodar_cenarios.py --cenarios sit3 --sem-ordem
"""
import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

import bw2cnf_var as enc
import interpretar
from busca_exaustiva import verificar_plano

PRINCIPAIS = ['sit1_sf4', 'sit2', 'sit3']
PASTA = enc.PASTA


def rodar_minisat(minisat, cnf, saida):
    p = subprocess.run([minisat, cnf, saida], capture_output=True, text=True)
    # minisat retorna 10 (SAT) ou 20 (UNSAT); outros codigos indicam erro
    if p.returncode not in (10, 20):
        raise RuntimeError(f'minisat falhou (codigo {p.returncode}): {p.stderr or p.stdout}')
    return p.returncode == 10


def rodar_cenario(nome, minisat, destino, max_h, sem_ordem):
    cfg = enc.CENARIOS[nome]
    ordem = [] if sem_ordem else cfg['ordem']
    pasta, res_nome = PASTA[nome]
    pasta = os.path.join(destino, pasta)
    print(f'\n=== {nome}  (ordem parcial: {"nao" if not ordem else "sim"}) ===')
    for T in range(max_h + 1):
        nvars, clauses, names, n_base = enc.build(cfg['initial'], cfg['goal'], T, ordem)
        with tempfile.TemporaryDirectory() as tmp:
            pref = os.path.join(tmp, 'trab01_blocos2SAT')
            cnf, mp = enc.write_files(pref, nvars, clauses, names)
            res = os.path.join(tmp, res_nome)
            sat = rodar_minisat(minisat, cnf, res)
            print(f'  T={T:2d}: {nvars:6d} vars, {len(clauses):8d} clausulas -> '
                  f'{"SATISFIABLE" if sat else "UNSATISFIABLE"}')
            if not sat:
                continue
            os.makedirs(pasta, exist_ok=True)
            for f in (cnf, mp, res):
                shutil.copy(f, pasta)
            mapa = interpretar.ler_mapa(mp)
            _, verd = interpretar.ler_resultado(res)
            plano = interpretar.acoes(mapa, verd)
            ok, msg = verificar_plano(cfg['initial'], cfg['goal'], [(b, y, p) for (_, b, y, p) in plano])
            # plano legivel no terminal (mesma saida do interpretar.py)
            for i, (t, b, y, p) in enumerate(plano, 1):
                print(f'     {i}. t={t}: {interpretar.frase(b, y, p)}')
            print(f'  -> plano com {len(plano)} acoes; verificacao independente: {msg}')
            print(f'  -> esperado (busca exaustiva / texto): {cfg["esperado"]}; '
                  f'{"OK" if T == cfg["esperado"] else "DIVERGE"}')
            print(f'  -> artefatos em {pasta}/')
            return T, ok
    print(f'  nenhum plano ate T={max_h}')
    return None, False


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--cenarios', nargs='+', choices=sorted(enc.CENARIOS))
    ap.add_argument('--todos', action='store_true', help='inclui Sf1, Sf2 e Sf3 da Situacao 1')
    ap.add_argument('--max-h', type=int, default=12)
    ap.add_argument('--minisat', default=shutil.which('minisat') or 'minisat')
    ap.add_argument('--saida', default='.')
    ap.add_argument('--sem-ordem', action='store_true')
    a = ap.parse_args()
    nomes = a.cenarios or (sorted(enc.CENARIOS) if a.todos else PRINCIPAIS)

    resumo = []
    for n in nomes:
        resumo.append((n, *rodar_cenario(n, a.minisat, a.saida, a.max_h, a.sem_ordem)))
    print('\nRESUMO')
    for n, T, ok in resumo:
        print(f'  {n:10s} menor T satisfativel = {T}  (esperado {enc.CENARIOS[n]["esperado"]}; '
              f'plano verificado: {"sim" if ok else "NAO"})')


if __name__ == '__main__':
    main()