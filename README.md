# Mundo dos Blocos de Tamanho Variável → SAT

Planejamento no Mundo dos Blocos com blocos de comprimentos diferentes, resolvido por **redução a SAT**: o problema é codificado em CNF (DIMACS), resolvido pelo `minisat` e a resposta numérica é traduzida de volta para um plano legível. Um verificador independente (BFS, sem SAT) confere os planos.

## Domínio

| Item | Valor |
|---|---|
| Blocos | `a`=1, `b`=1, `c`=2, `d`=3 (comprimento em slots) |
| Mesa | 6 slots (pontos 0..6) |
| Níveis | 0..3 (0 = mesa) |
| Ação | `move(b, y, p)`: move o bloco `b` para cima de `y` (ou da mesa `T`) começando no ponto `p` |

Regras da ação (pré-condições): P1 `b` livre · P2 destino válido · P3 sobreposição com `y` · P4 slots livres no nível-alvo · P5 folga vertical · P6 estabilidade (≥ ⌈l(b)/2⌉ slots apoiados) · P7 ação não nula.

## Arquivos

| Arquivo | Função |
|---|---|
| `bw2cnf_var.py` | Define blocos e cenários; gera o CNF (`.cnf`) e o mapa de variáveis (`.map`) |
| `rodar_cenarios.py` | Automatiza tudo: gera o CNF, roda o minisat com `T = 0, 1, 2, …` até `SATISFIABLE`, interpreta e verifica o plano |
| `interpretar.py` | Traduz a saída numérica do minisat (usando o `.map`) em um plano em português |
| `busca_exaustiva.py` | Verificador independente (BFS): acha o plano mínimo e valida planos do SAT |

## Requisitos

- Python 3.8+ (somente biblioteca padrão)
- [`minisat`](http://minisat.se/) no `PATH` (`sudo apt install minisat`)

## Cenários

| Nome | Descrição | Menor plano |
|---|---|---|
| `sit1_sf4` | Situação 1 (com ordem parcial: `d` na mesa antes de `a` sobre `c`) | 4 |
| `sit2` | Situação 2, S0 → S5 (com ordem parcial) | 5 |
| `sit3` | Situação 3, S0 → S7 (com ordem parcial) | 6 |
| `sit1_sf1`, `sit1_sf2`, `sit1_sf3` | Metas extras da Situação 1 (sem ordem parcial) | 9, 10, 10 |

## Uso (fluxo do Manual, Seção 6)

São 3 passos: **gerar CNF → rodar o miniSAT → interpretar**.

**1. Gerar o CNF** — sem argumentos, cria as três pastas de uma vez, cada uma com o `.cnf` e o `.map`:

```bash
python3 bw2cnf_var.py
```

```
[sit1_sf4] 1146 variaveis, 31390 clausulas (...), horizonte T=4
  Arquivos: situacao1/trab01_blocos2SAT.cnf, situacao1/trab01_blocos2SAT.map
[sit2] ...  -> situacao2/
[sit3] ...  -> situacao3/
```

Para gerar só um cenário (ou outro horizonte):

```bash
python3 bw2cnf_var.py --cenario sit2
python3 bw2cnf_var.py --cenario sit3 --horizon 6
python3 bw2cnf_var.py --cenario sit1_sf1 sit1_sf2     # extras, em situacao1/extras_*
```

**2. Executar o miniSAT** — grava o `resultadoX.txt` na mesma pasta:

```bash
minisat situacao1/trab01_blocos2SAT.cnf situacao1/resultado1.txt
minisat situacao2/trab01_blocos2SAT.cnf situacao2/resultado2.txt
minisat situacao3/trab01_blocos2SAT.cnf situacao3/resultado3.txt
```

**3. Interpretar o resultado** — o `.map` é lido automaticamente da pasta do resultado:

```bash
python3 interpretar.py situacao3/resultado3.txt --verbose
```

```
PLANO ENCONTRADO (6 acoes):
1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
...
ESTADO FINAL (t=6): ...
RELACOES 'on' em t=6: ...
```

Os horizontes padrão (4, 5 e 6) são os mínimos. Para provar a otimalidade, rode com `T = 0, 1, 2, …` até o primeiro `SATISFIABLE`.

### Atalho: automatizar os 4 passos

`rodar_cenarios.py` repete o fluxo acima para cada `T` crescente e já confere o plano com o verificador independente:

```bash
python3 rodar_cenarios.py                        # sit1_sf4, sit2 e sit3
python3 rodar_cenarios.py --todos                # inclui sit1_sf1..sf3
python3 rodar_cenarios.py --cenarios sit3 --sem-ordem
python3 rodar_cenarios.py --max-h 10 --minisat /caminho/minisat
```

Opções: `--max-h` (padrão 12), `--minisat`, `--saida` (diretório base das pastas), `--sem-ordem`.

### Verificador independente (BFS, sem SAT)

```bash
python3 busca_exaustiva.py           # plano mínimo de todos os cenários
python3 busca_exaustiva.py sit3
```

## Pastas e arquivos gerados

Ao rodar, uma pasta por situação é criada contendo exatamente três arquivos:

```
situacao1/
├── trab01_blocos2SAT.cnf     # fórmula em DIMACS
├── trab01_blocos2SAT.map     # ID da variável -> símbolo (ex.: 42 mv(d,c,0,0))
├── resultado1.txt            # saída bruta do minisat
├── extras_sf1/               # (só com --todos) mesma estrutura, resultado_sf1.txt
├── extras_sf2/               #                  resultado_sf2.txt
└── extras_sf3/               #                  resultado_sf3.txt
situacao2/
├── trab01_blocos2SAT.cnf
├── trab01_blocos2SAT.map
└── resultado2.txt
situacao3/
├── trab01_blocos2SAT.cnf
├── trab01_blocos2SAT.map
└── resultado3.txt
```

O passo 1 cria as pastas com `.cnf` e `.map`; o `resultadoX.txt` aparece no passo 2. O `rodar_cenarios.py` faz tudo e guarda os arquivos do **menor horizonte satisfatível**.

> **Regra de ouro:** o `.map` é indispensável. O minisat só devolve inteiros; sem o mapa correspondente à *mesma* execução, a saída não tem significado.

## Como a codificação funciona (resumo)

- **Variáveis base:** `at(b,p,t)` posição, `lev(b,l,t)` nível, `clr(b,t)` topo livre, `mv(b,y,p,t)` ação.
- **Auxiliares:** `cb`/`cov` (cobertura de slots), `pos` e `o_on` (ordem parcial).
- **11 grupos de cláusulas:** estado inicial, meta, unicidade de posição/nível, exclusão horizontal, estabilidade, clear, pré-condições, efeitos, frame axioms e ação única por passo.
- **Ordem parcial** `φ1 <ₚ φ2`: `φ2(t)` só vale se `φ1(t')` valeu para algum `t' < t`.
- A relação `on` **não** é codificada; é derivada em `interpretar.py` (`on(b,y)` ⇔ `lev(b)=l`, `lev(y)=l-1` e spans sobrepostos; vários apoios = ponte).
- O menor `T` satisfatível é o comprimento mínimo do plano.

## Exemplo de saída

```
=== sit3  (ordem parcial: sim) ===
  T= 5:   1392 vars,    38962 clausulas -> UNSATISFIABLE
  T= 6:   1638 vars,    46534 clausulas -> SATISFIABLE
     1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
     ...
  -> plano com 6 acoes; verificacao independente: plano legal e atinge a meta
```
