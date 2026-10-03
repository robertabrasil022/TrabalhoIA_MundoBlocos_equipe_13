::: resumo
Este trabalho propõe uma representação em Lógica de Primeira Ordem para
o planejamento no Mundo dos Blocos com blocos de tamanhos diferentes,
levando em conta posição horizontal, empilhamento e estabilidade. A
representação é codificada em CNF e resolvida com um SAT solver, e os
planos obtidos são comparados com os planos feitos manualmente em três
cenários.
:::

# Introdução

O Mundo dos Blocos é um domínio clássico de planejamento em Inteligência
Artificial. Neste trabalho ele é estendido para blocos de comprimentos
diferentes, sobre uma mesa com posições horizontais definidas. Com isso,
um bloco pode ocupar vários slots, apoiar-se em mais de um bloco
(ponte), deixar espaços vazios embaixo de si e precisa estar
equilibrado.

O objetivo é descrever esse mundo em Lógica de Primeira Ordem, construir
planos manualmente, traduzir a descrição para CNF e gerar planos com um
SAT solver, comparando-os com os planos manuais nas Situações 1, 2 e 3.

# Descrição Formal do Mundo dos Blocos de Tamanho Variado {#sec:formal}

## Domínio

::: center
  -------------- --------------------------------------------------------------------------------------
  Blocos         $B = \{a, b, c, d\}$, mesa $T$
  Comprimentos   $\ell(a) = \ell(b) = 1,\ \ell(c) = 2,\ \ell(d) = 3$
  Pontos         $X = \{0, 1, \dots, 6\}$
  Slots          $s_i = [i, i+1],\ i \in \{0, \dots, 5\}$
  Níveis         $l \in \{0, 1, 2, 3\}$ (0 = mesa)
  Tempo          $t \in \{0, \dots, H\}$, onde $H$ é o horizonte (número de passos)
  Span           $\mathit{span}(b, p) = \{p, \dots, p + \ell(b) - 1\}$, com $0 \le p \le 6 - \ell(b)$
  -------------- --------------------------------------------------------------------------------------
:::

## Predicados

::: center
  Predicado                        Significado
  -------------------------------- ---------------------------------------------------
  $\mathit{at}(b, p, t)$           $b$ começa no ponto $p$
  $\mathit{lev}(b, l, t)$          $b$ está no nível $l$
  $\mathit{cov}(b, s, l, t)$       $b$ ocupa o slot $s$ no nível $l$
  $\mathit{overlap}(b, p, y, q)$   spans de $b$ (em $p$) e $y$ (em $q$) se sobrepõem
  $\mathit{on}(b, y, t)$           $b$ está apoiado em $y \in B \cup \{T\}$
  $\mathit{clr}(b, t)$             nada está sobre $b$
:::

Apenas $\mathit{at}$ e $\mathit{lev}$ são fluentes básicos. Os demais
são derivados: $$\begin{align*}
\mathit{cov}(b, s, l, t) &\leftrightarrow \exists p\, \big(\mathit{at}(b, p, t) \land \mathit{lev}(b, l, t) \land s \in \mathit{span}(b, p)\big)\\
\mathit{overlap}(b, p, y, q) &\leftrightarrow p < q + \ell(y) \land q < p + \ell(b)\\
\mathit{on}(b, T, t) &\leftrightarrow \mathit{lev}(b, 0, t)\\
\mathit{on}(b, y, t) &\leftrightarrow \exists p, q, l\, \big(\mathit{at}(b, p, t) \land \mathit{at}(y, q, t) \land \mathit{lev}(b, l, t)\\
&\qquad\qquad \land \mathit{lev}(y, l-1, t) \land \mathit{overlap}(b, p, y, q)\big)\\
\mathit{clr}(b, t) &\leftrightarrow \neg \exists x\, \mathit{on}(x, b, t)
\end{align*}$$

## Restrições de estado

$$\begin{align*}
\text{Unicidade:}\quad & \forall b\, \exists! p\ \mathit{at}(b, p, t) \qquad \forall b\, \exists! l\ \mathit{lev}(b, l, t)\\[4pt]
\text{Exclusão:}\quad & \forall b \ne b',\, s,\, l\ \ \neg\big(\mathit{cov}(b, s, l, t) \land \mathit{cov}(b', s, l, t)\big)\\[4pt]
\text{Estabilidade:}\quad & \mathit{at}(b, p, t) \land \mathit{lev}(b, l, t) \land l > 0 \rightarrow\\
& \big|\{ s \in \mathit{span}(b, p) : \exists b' \ne b\ \mathit{cov}(b', s, l-1, t) \}\big| \ge \lceil \ell(b)/2 \rceil
\end{align*}$$

A contagem equivale a uma disjunção finita. Assim, $d$ precisa de 2
slots apoiados (o que permite a ponte) e $c$ precisa de 1.

## A ação move {#sec:move}

$\mathit{move}(b, y, p, t)$: mover $b$ para cima de $y$ (bloco ou mesa),
começando no ponto $p$. O nível de destino é $l^* = 0$ se $y = T$, e
$l^* = \mathit{lev}(y) + 1$ se $y \in B$. Na codificação CNF (Seção 3),
cada ação corresponde à variável $\mathit{mv}(b, y, p, t)$.

::: center
       Precondição             Manual  Fórmula
  ---- ---------------------- -------- -----------------------------------------------------------------------------------------
  P1   $b$ livre                 1     $\mathit{clr}(b, t)$
  P2   destino válido            --    $y \ne b,\ 0 \le p \le 6 - \ell(b)$
  P3   sobreposição com $y$      4     $y \in B \rightarrow \mathit{at}(y, q, t) \land \mathit{overlap}(b, p, y, q)$
  P4   slots livres              5     $\forall s \in \mathit{span}(b,p),\, z \ne b\ \neg \mathit{cov}(z, s, l^*, t)$
  P5   folga vertical           nova   $\forall s \in \mathit{span}(b,p),\, l > l^*,\, z \ne b\ \neg \mathit{cov}(z, s, l, t)$
  P6   estabilidade              --    regra de estabilidade em $(p, l^*)$, se $l^* > 0$
  P7   ação não nula             3     $\neg\big(\mathit{at}(b, p, t) \land \mathit{lev}(b, l^*, t)\big)$
:::

A coluna "Manual" indica a precondição correspondente no Manual. A
precondição 2 do Manual ($\mathit{clr}(y)$) foi removida
(Seção [2.7](#sec:ajustes-manual){reference-type="ref"
reference="sec:ajustes-manual"}).

::: center
  Efeitos    (posição anterior de $b$: $p_0$, $l_0$)
  ---------- -----------------------------------------------------------------------------------------
  *add*      $\mathit{at}(b, p, t+1)$, $\mathit{lev}(b, l^*, t+1)$
  *add*      $\mathit{clr}(z, t+1)$ para cada antigo apoio $z$ que ficou livre
  *delete*   $\mathit{at}(b, p_0, t+1)$ se $p_0 \ne p$; $\mathit{lev}(b, l_0, t+1)$ se $l_0 \ne l^*$
  *delete*   $\mathit{clr}(y', t+1)$ para todo $y'$ sob o novo span (todos os apoios)
:::

**Persistência e ação única.** O que não é afetado pela ação continua
igual, e ocorre exatamente uma ação por instante: $$\begin{gather*}
\mathit{at}(b, p, t) \land \neg \mathit{at}(b, p, t+1) \rightarrow \textstyle\bigvee_{y, p'} \mathit{move}(b, y, p', t) \quad \text{(análogo para } \mathit{lev})\\
\textstyle\bigvee_{\alpha} \mathit{move}(\alpha, t) \qquad \neg \mathit{move}(\alpha, t) \lor \neg \mathit{move}(\beta, t) \quad \text{para ações distintas } \alpha, \beta
\end{gather*}$$ Com isso, o plano tem exatamente $H$ ações, e o menor
$H$ satisfatível é o tamanho do plano mínimo.

## Elementos novos e ações associadas

::: center
  Elemento                             Tipo         Ações associadas
  ------------------------------------ ------------ ----------------------------------------------------------------------------------------------------------
  $\ell(b)$                            estático     nenhuma
  $\mathit{at}(b, p, t)$               fluente      *add* por $\mathit{move}(b, \cdot, p, t)$; *delete* da posição antiga
  $\mathit{lev}(b, l, t)$              fluente      *add* de $l^*$ por $\mathit{move}(b, y, \cdot, t)$; *delete* do nível antigo
  $\mathit{clr}(y, t)$                 fluente      *delete* quando um bloco passa a cobrir $y$ (inclusive ponte); *add* quando o último bloco sobre $y$ sai
  $\mathit{cov}$, $\mathit{overlap}$   derivados    mudam junto com $\mathit{at}$ e $\mathit{lev}$
  $\mathit{on}(b, y, t)$               derivado     muda só por $\mathit{move}(b, \cdot, \cdot, t)$
  estabilidade                         invariante   checada em P6; preservada, pois apoio nunca está livre
:::

## Ordem parcial {#sec:ordem}

$\varphi_1 \prec_P \varphi_2$ exige que $\varphi_1$ ocorra antes de
$\varphi_2$:
$$\forall t\ \big(\varphi_2(t) \rightarrow \exists t' < t\ \varphi_1(t')\big)$$
Exemplo usado: $\varphi_1(t) \equiv \mathit{lev}(d, 0, t)$ ($d$ na mesa)
e $\varphi_2(t) \equiv \mathit{on}(a, c, t)$ ($a$ sobre $c$). Em CNF,
com $o_t$ auxiliar para $\mathit{on}(a, c, t)$: $$\begin{gather*}
\neg o_t \lor \mathit{lev}(d, 0, 0) \lor \dots \lor \mathit{lev}(d, 0, t-1)\\
\neg \mathit{at}(a, p, t) \lor \neg \mathit{lev}(a, l, t) \lor \neg \mathit{at}(c, q, t) \lor \neg \mathit{lev}(c, l-1, t) \lor o_t
\end{gather*}$$ a segunda cláusula para cada $p, q$ com spans
sobrepostos. A precedência é estrita ($t' < t$). Em $t = 0$ a primeira
cláusula fica só $\neg o_0$.

## Ajustes em relação ao Manual {#sec:ajustes-manual}

::: center
  Ajuste                         Motivo
  ------------------------------ -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  Remoção de $\mathit{clr}(y)$   Impede dois blocos lado a lado sobre um bloco maior e torna $S_{f1}$ e $S_{f2}$ (Situação 1) e $S_5$ (Situação 2) inalcançáveis. P4 já garante os slots livres. Cláusulas na Seção [3.3](#sec:ajuste){reference-type="ref" reference="sec:ajuste"}.
  Folga vertical (P5)            O Manual proíbe ocupar o slot sob a ponte, mas não formaliza. Sem P5, $S_{f3}$ sairia em 2 ações deslizando $a$ sob $d$. Cláusulas na Seção [3.4](#sec:ponte){reference-type="ref" reference="sec:ponte"}.
  Efeitos completos              Liberar o antigo apoio e ocupar todos os apoios da ponte.
:::

# Codificação CNF

Para usar um SAT solver, o mundo descrito em lógica de primeira ordem é
traduzido para lógica proposicional. Cada fato possível do mundo vira
uma variável que só pode ser verdadeira ou falsa, e as regras do mundo
viram cláusulas sobre essas variáveis. Se existe uma atribuição que
satisfaz todas as cláusulas, ela contém o plano. Neste texto, $T$ é o
número de passos do plano e também o símbolo da mesa, como no Manual; o
contexto indica qual dos dois é.

## Variáveis proposicionais

Para um horizonte de $T$ passos, são criadas quatro famílias de
variáveis (Tabela [1](#tab:vars){reference-type="ref"
reference="tab:vars"}).

::: {#tab:vars}
  Variável                 Significado                                                                                        Índices
  ------------------------ -------------------------------------------------------------------------------------------------- -------------------------------------------------
  $\mathit{at}(b,p,t)$     o bloco $b$ começa no ponto $p$ no instante $t$                                                    $b\in B$, $p\in[0,6-\ell(b)]$, $t\in[0,T]$
  $\mathit{lev}(b,l,t)$    $b$ está no nível $l$ no instante $t$                                                              $l\in[0,3]$
  $\mathit{clr}(b,t)$      o topo de $b$ está livre no instante $t$                                                           $t\in[0,T]$
  $\mathit{mv}(b,y,p,t)$   em $t$, $b$ é movido para cima de $y$ (ou da mesa $T$), começando em $p$; o efeito vale em $t+1$   $y\in(B\cup\{T\})\setminus\{b\}$, $t\in[0,T-1]$

  : Variáveis proposicionais da codificação.
:::

A relação $on$ não é codificada. Ela é derivada depois, a partir de
$\mathit{at}$, $\mathit{lev}$ e da sobreposição dos spans (Seção 7).

Na Situação 2, com $T=5$, os blocos $a$, $b$, $c$ e $d$ têm 6, 6, 5 e 4
posições válidas, somando 21. Então $\mathit{at}$ tem $21\cdot 6=126$
variáveis, $\mathit{lev}$ tem $4\cdot 4\cdot 6=96$, $\mathit{clr}$ tem
$4\cdot 6=24$ e $\mathit{mv}$ tem $4\cdot 21\cdot 5=420$, num total de
666 variáveis. As variáveis auxiliares $\mathit{cov}$ do grupo 6 ficam
fora dessa conta.

## Grupos de cláusulas

1.  **Estado inicial.** Cláusulas unitárias que fixam $\mathit{at}$ e
    $\mathit{lev}$ em $t=0$ com as posições do estado inicial. Exemplo:
    $\mathit{at}(c,0,0)$ e $\mathit{lev}(c,0,0)$.

2.  **Meta.** Cláusulas unitárias que fixam $\mathit{at}$ e
    $\mathit{lev}$ em $t=T$ com as posições do estado final.

3.  **Unicidade de posição.** Em cada instante, cada bloco tem
    exatamente um ponto inicial. Pelo menos um:
    $\bigvee_p \mathit{at}(b,p,t)$. No máximo um:
    $\neg\mathit{at}(b,p_1,t)\lor\neg\mathit{at}(b,p_2,t)$ para
    $p_1<p_2$.

4.  **Unicidade de nível.** Mesma ideia para $\mathit{lev}$: cada bloco
    está em exatamente um nível em cada instante.

5.  **Exclusão horizontal.** Dois blocos no mesmo nível não podem cobrir
    o mesmo slot. Para $b\neq b'$ com spans que se sobrepõem em $p$ e
    $p'$:
    $$\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(b,l,t)\lor\neg\mathit{at}(b',p',t)\lor\neg\mathit{lev}(b',l,t).$$

6.  **Estabilidade.** Um bloco no nível $l>0$ precisa ter pelo menos
    $\lceil\ell(b)/2\rceil$ dos slots do seu span ocupados no nível
    $l-1$. Seja $\mathit{cov}(s,l,t)$ a afirmação "o slot $s$ é coberto
    por algum bloco no nível $l$ no instante $t$". Para cada $b$, $p$,
    $l>0$ e cada conjunto $S$ de slots do span com
    $|S|=\ell(b)-\lceil\ell(b)/2\rceil+1$:
    $$\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(b,l,t)\lor\bigvee_{s\in S}\mathit{cov}(s,l-1,t).$$
    Para $a$ e $b$ ($\ell=1$) sai uma cláusula com um único
    $\mathit{cov}$. Para $c$ ($\ell=2$), uma cláusula com os dois slots.
    Para $d$ ($\ell=3$), uma cláusula por par de slots, o que exige pelo
    menos dois dos três apoios. Como $\mathit{cov}$ é uma disjunção de
    conjunções $\mathit{at}\land\mathit{lev}$, no CNF ele vira uma
    variável auxiliar definida por equivalência. Blocos no nível 0 não
    precisam de apoio, pois estão na mesa.

7.  **Clear.** $\mathit{clr}(b,t)$ é verdadeira exatamente quando nenhum
    bloco está no nível acima de $b$ cobrindo algum slot do seu span.
    Para $b$ em $(p,l)$: $$\begin{align*}
    &\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(b,l,t)\lor\neg\mathit{cov}(s,l+1,t)\lor\neg\mathit{clr}(b,t) \quad \text{para cada } s\in\text{span}(b,p),\\
    &\mathit{clr}(b,t)\lor\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(b,l,t)\lor\textstyle\bigvee_{s\in\text{span}(b,p)}\mathit{cov}(s,l+1,t).
    \end{align*}$$ Como $\mathit{clr}$ é definida em todo instante por
    essas cláusulas, ela se atualiza sozinha quando um bloco sai de cima
    de outro, inclusive nos dois apoios de uma ponte.

8.  **Pré-condições de $\mathit{mv}(b,y,p,t)$.** Sendo $m$ o nível de
    $y$ (o nível-alvo é $m+1$, ou $0$ se $y=T$):

    1.  $b$ tem o topo livre:
        $\neg\mathit{mv}(b,y,p,t)\lor\mathit{clr}(b,t)$.

    2.  (Ajustada, ver Seção [3.3](#sec:ajuste){reference-type="ref"
        reference="sec:ajuste"}.)

    3.  O destino não é a posição atual:
        $\neg\mathit{mv}(b,y,p,t)\lor\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(y,m,t)\lor\neg\mathit{lev}(b,m+1,t)$.
        Para $y=T$, a cláusula é
        $\neg\mathit{mv}(b,T,p,t)\lor\neg\mathit{at}(b,p,t)\lor\neg\mathit{lev}(b,0,t)$.

    4.  Se $y$ é bloco, o span de $b$ em $p$ sobrepõe o de $y$:
        $\neg\mathit{mv}(b,y,p,t)\lor\neg\mathit{at}(y,q,t)$ para cada
        $q$ cujo span não sobrepõe o de $b$ em $p$.

    5.  Os slots cobertos por $b$ no nível-alvo estão livres. Para cada
        $x\neq b$ em $(q,m+1)$ com span sobrepondo o de $b$ em $p$:
        $\neg\mathit{mv}(b,y,p,t)\lor\neg\mathit{lev}(y,m,t)\lor\neg\mathit{at}(x,q,t)\lor\neg\mathit{lev}(x,m+1,t)$.
        Para $y=T$:
        $\neg\mathit{mv}(b,T,p,t)\lor\neg\mathit{at}(x,q,t)\lor\neg\mathit{lev}(x,0,t)$.

    A estabilidade do destino não precisa de cláusula própria aqui, pois
    o grupo 6 aplicado em $t+1$ já a exige. A cláusula do slot sob a
    ponte, que o Manual não traz, está na
    Seção [3.4](#sec:ponte){reference-type="ref" reference="sec:ponte"}.

9.  **Efeitos de $\mathit{mv}(b,y,p,t)$.** $$\begin{align*}
    &\mathit{mv}(b,y,p,t)\to\mathit{at}(b,p,t+1),\\
    &\mathit{mv}(b,y,p,t)\land\mathit{lev}(y,m,t)\to\mathit{lev}(b,m+1,t+1) && (\text{ou } \mathit{lev}(b,0,t+1) \text{ se } y=T),\\
    &\mathit{mv}(b,y,p,t)\to\neg\mathit{clr}(y,t+1) && (\text{se } y \text{ é bloco}).
    \end{align*}$$ Que $b$ deixa a posição e o nível anteriores segue da
    unicidade (grupos 3 e 4). Que os apoios antigos de $b$ voltam a
    ficar livres segue do grupo 7.

10. **Frame axioms.** O que não muda no passo continua igual. Seja
    $M_b(t)=\bigvee_{y,p'}\mathit{mv}(b,y,p',t)$. Então
    $$\mathit{at}(b,p,t)\land\neg M_b(t)\to\mathit{at}(b,p,t+1)
    \qquad\text{e}\qquad
    \mathit{lev}(b,l,t)\land\neg M_b(t)\to\mathit{lev}(b,l,t+1).$$ Para
    $\mathit{clr}$ não é preciso axioma próprio, pois o grupo 7 a define
    em todo instante.

11. **Ação única por passo.** Em cada $t$ exatamente uma variável
    $\mathit{mv}$ é verdadeira: pelo menos uma,
    $\bigvee \mathit{mv}(\cdot,\cdot,\cdot,t)$, e no máximo uma,
    $\neg\mathit{mv}_i\lor\neg\mathit{mv}_j$ para cada par de variáveis
    $\mathit{mv}$ do instante $t$.

## Ajuste na pré-condição 2 de move {#sec:ajuste}

A pré-condição 2 do Manual exige $\mathit{clr}(y,t)$, isto é, que o topo
inteiro de $y$ esteja livre. Com essa leitura literal, nenhum bloco
poderia ser colocado sobre um $y$ que já carrega outro bloco, mesmo em
uma parte livre do seu topo.

Isso impede a Situação 2. Em $S_0$ e em $S_5$, os blocos $a$ e $b$ estão
lado a lado sobre $c$. Em $S_5$, o primeiro dos dois a ser colocado
sobre $c$ deixaria $\mathit{clr}(c)$ falso, e a pré-condição literal
bloquearia o segundo. Como $c$ é o único bloco do nível 1 que serve de
apoio aos dois, $S_5$ não seria alcançável a partir de $S_0$.

O ajuste adotado é retirar $\mathit{clr}(y,t)$ como condição
independente. O que realmente importa é que os slots onde $b$ vai pousar
estejam livres, e isso já é exigido pela pré-condição 5. O bloco que se
move continua precisando de $\mathit{clr}(b,t)$, e o efeito
$\neg\mathit{clr}(y,t+1)$ continua correto, pois $y$ passa a ter $b$ em
cima.

## Cláusula do slot sob a ponte {#sec:ponte}

No estado inicial da Situação 1, o bloco $d$ está em ponte sobre $a$ e
$b$, com o slot $s_4$ vazio no nível 0 e coberto por $d$ no nível 1. A
pré-condição 5 só olha o nível-alvo. Se o nível-alvo é o 0, o slot $s_4$
aparece livre, e nada impediria colocar um bloco ali embaixo de $d$. O
modelo do Manual considera esse slot bloqueado, mas nenhuma cláusula diz
isso.

A regra geral é: um bloco não pode pousar em um slot do nível $l$ se
algum bloco em um nível maior que $l$ cobre esse slot. Se o slot já tem
bloco no nível $l$, a pré-condição 5 já impede. A cláusula nova cobre o
caso do slot vazio. Para cada $x\neq b$ em $(q,k)$ com span sobrepondo o
de $b$ em $p$ e $k>m+1$:
$$\neg\mathit{mv}(b,y,p,t)\lor\neg\mathit{lev}(y,m,t)\lor\neg\mathit{at}(x,q,t)\lor\neg\mathit{lev}(x,k,t).$$
Para $y=T$, o nível-alvo é 0 e vale, para todo $k\geq 1$:
$$\neg\mathit{mv}(b,T,p,t)\lor\neg\mathit{at}(x,q,t)\lor\neg\mathit{lev}(x,k,t).$$

# Exemplos dos Três Cenários

## Situação 1

### Estados inicial e meta

<figure id="fig:sit1" data-latex-placement="ht">
<p><img src="./sit1_S0.png" alt="image" /> <img src="./sit1_Sf4.png"
alt="image" /></p>
<figcaption>Estado inicial <span
class="math inline"><em>S</em><sub>0</sub></span> e meta <span
class="math inline"><em>S</em><sub><em>f</em>4</sub></span> da Situação
1.</figcaption>
</figure>

$$\begin{align*}
S_0 &:\ \mathit{at}(c,0) \land \mathit{lev}(c,0) \land \mathit{at}(a,3) \land \mathit{lev}(a,0)\\
&\quad \land \mathit{at}(b,5) \land \mathit{lev}(b,0) \land \mathit{at}(d,3) \land \mathit{lev}(d,1)\\
S_{f4} &:\ \mathit{at}(c,0) \land \mathit{lev}(c,0) \land \mathit{at}(a,0) \land \mathit{lev}(a,1)\\
&\quad \land \mathit{at}(d,2) \land \mathit{lev}(d,0) \land \mathit{at}(b,5) \land \mathit{lev}(b,0)
\end{align*}$$

::: center
  Estado     Relações $\mathit{on}$
  ---------- ------------------------------------------------------------------------------------------------
  $S_0$      $\mathit{on}(c,T),\ \mathit{on}(a,T),\ \mathit{on}(b,T),\ \mathit{on}(d,a),\ \mathit{on}(d,b)$
  $S_{f4}$   $\mathit{on}(c,T),\ \mathit{on}(d,T),\ \mathit{on}(b,T),\ \mathit{on}(a,c)$
:::

### Plano manual

::: {#tab:plano-sit1}
  Passo   Ação                       Verificação
  ------- -------------------------- ---------------------------------------------------------------------------------
  $t=0$   $\mathit{move}(d, c, 0)$   $d$ livre; nível 1, slots 0--2 livres; apoio em 0 e 1 ($2 \ge 2$).
  $t=1$   $\mathit{move}(a, b, 5)$   $a$ livre; slot 5 livre no nível 1; apoio em $b$.
  $t=2$   $\mathit{move}(d, T, 2)$   $d$ livre; slots 2--4 livres no nível 0, nada acima.
  $t=3$   $\mathit{move}(a, c, 0)$   $a$ livre; slot 0 livre no nível 1; apoio em $c$. Em $t=4$ o estado é $S_{f4}$.

  : Plano manual da Situação 1, de $S_0$ até $S_{f4}$.
:::

#### Por que 4 ações é o mínimo.

$d$ precisa de 2 ações (não há 3 slots livres consecutivos em $S_0$).
$a$ também precisa de 2, pois só fica livre quando $d$ vai para $p = 0$
sobre $c$, cobrindo o destino de $a$. Logo, 4 ações é o mínimo,
confirmado por busca exaustiva.

#### Ordem parcial.

$d$ chega à mesa em $t = 3$ e $a$ fica sobre $c$ em $t = 4$, então
$\varphi_1 \prec_P \varphi_2$
(Seção [2.6](#sec:ordem){reference-type="ref" reference="sec:ordem"}) é
respeitada.

#### Outras metas.

Planos mínimos por busca exaustiva: $S_{f1}$ com 9 ações, $S_{f2}$ com
10 e $S_{f3}$ com 10.

### Codificação em CNF

Os grupos 1 e 2 são as oito cláusulas unitárias de $S_0$ (em $t=0$) e as
oito de $S_{f4}$ (em $t=4$), escritas acima. Com $H=4$ há
$21\cdot 5=105$ variáveis $\mathit{at}$, $4\cdot 4\cdot 5=80$ de
$\mathit{lev}$, $4\cdot 5=20$ de $\mathit{clr}$ e $84\cdot 4=336$ de
$\mathit{mv}$, num total de 541, mais as auxiliares $\mathit{cov}$ e as
$o_0,\dots,o_4$ da ordem parcial. No script:

    INITIAL = {'c': (0,0), 'a': (3,0), 'b': (5,0), 'd': (3,1)}
    GOAL    = {'c': (0,0), 'a': (0,1), 'd': (2,0), 'b': (5,0)}
    HORIZON = 4

Pelo plano manual, o resultado esperado é `UNSATISFIABLE` para
$H=0,\dots,3$ e `SATISFIABLE` para $H=4$, com ou sem a cláusula de ordem
parcial.

## Situação 2

### Estados inicial e meta

Cada ponto é dado como $(p,l)$, com $p$ o ponto inicial e $l$ o nível. O
estado inicial $S_0$ é $$\begin{align*}
&\mathit{at}(c,0,0)\land\mathit{lev}(c,0,0), \qquad \mathit{at}(d,3,0)\land\mathit{lev}(d,0,0),\\
&\mathit{at}(a,0,0)\land\mathit{lev}(a,1,0), \qquad \mathit{at}(b,1,0)\land\mathit{lev}(b,1,0),
\end{align*}$$ com as relações $on(c,T,0)$, $on(d,T,0)$, $on(a,c,0)$ e
$on(b,c,0)$. O slot $s_2$ da mesa está vazio e livre.

O estado meta $S_5$, em $t=5$, é $$\begin{align*}
&\mathit{at}(d,3,5)\land\mathit{lev}(d,0,5), \qquad \mathit{at}(c,4,5)\land\mathit{lev}(c,1,5),\\
&\mathit{at}(a,4,5)\land\mathit{lev}(a,2,5), \qquad \mathit{at}(b,5,5)\land\mathit{lev}(b,2,5),
\end{align*}$$ com as relações $on(d,T,5)$, $on(c,d,5)$, $on(a,c,5)$ e
$on(b,c,5)$.

### Plano manual

<figure id="fig:sit2-estados" data-latex-placement="ht">
<div class="minipage">
<p><span class="math inline"><em>t</em> = 0</span> (S<span
class="math inline"><sub>0</sub></span>)<br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"><strong>a</strong></th>
<th style="text-align: center;"><strong>b</strong></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
</tr>
</thead>
<tbody>
<tr>
<td colspan="2" style="text-align: center;"><strong>c</strong></td>
<td style="text-align: center;"></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<div class="minipage">
<p><span class="math inline"><em>t</em> = 1</span><br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"></th>
<th style="text-align: center;"><strong>b</strong></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
</tr>
</thead>
<tbody>
<tr>
<td colspan="2" style="text-align: center;"><strong>c</strong></td>
<td style="text-align: center;"><strong>a</strong></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<div class="minipage">
<p><span class="math inline"><em>t</em> = 2</span><br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"><strong>b</strong></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
</tr>
</thead>
<tbody>
<tr>
<td colspan="2" style="text-align: center;"><strong>c</strong></td>
<td style="text-align: center;"><strong>a</strong></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<div class="minipage">
<p><span class="math inline"><em>t</em> = 3</span><br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"><strong>b</strong></th>
<th colspan="2" style="text-align: center;"><strong>c</strong></th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"><strong>a</strong></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<div class="minipage">
<p><span class="math inline"><em>t</em> = 4</span><br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"><strong>a</strong></th>
<th style="text-align: center;"></th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"><strong>b</strong></td>
<td colspan="2" style="text-align: center;"><strong>c</strong></td>
</tr>
<tr>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<div class="minipage">
<p><span class="math inline"><em>t</em> = 5</span> (S<span
class="math inline"><sub>5</sub></span>)<br />
</p>
<table>
<thead>
<tr>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"></th>
<th style="text-align: center;"><strong>a</strong></th>
<th style="text-align: center;"><strong>b</strong></th>
</tr>
</thead>
<tbody>
<tr>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td colspan="2" style="text-align: center;"><strong>c</strong></td>
</tr>
<tr>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td style="text-align: center;"></td>
<td colspan="3" style="text-align: center;"><strong>d</strong></td>
</tr>
<tr>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>0</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>1</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>2</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>3</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>4</sub></span></td>
<td style="text-align: center;"><span
class="math inline"><em>s</em><sub>5</sub></span></td>
</tr>
</tbody>
</table>
</div>
<figcaption>Estados da Situação 2 ao longo do plano manual. As colunas
são os slots <span class="math inline"><em>s</em><sub>0</sub></span> a
<span class="math inline"><em>s</em><sub>5</sub></span> e as linhas são
os níveis (a mesa é o nível 0).</figcaption>
</figure>

::: {#tab:plano-sit2}
  Passo   Ação                     Verificação
  ------- ------------------------ --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  $t=0$   $\mathit{mv}(a,T,2,0)$   $a$ tem o topo livre. O destino é a mesa e o slot $s_2$ está vazio, sem bloco acima dele. Em $t=1$, $a$ está fora de $c$ e $b$ continua sobre $c$.
  $t=1$   $\mathit{mv}(b,d,3,1)$   $b$ tem o topo livre. Em $p=3$ ele sobrepõe $d$ e o slot $s_3$ do nível 1 está livre. Apoio: $s_3$ está sobre $d$, e $1\geq\lceil 1/2\rceil$. Agora $c$ fica com o topo livre.
  $t=2$   $\mathit{mv}(c,d,4,2)$   $c$ tem o topo livre, pois $a$ e $b$ já saíram. Em $p=4$ ele cobre $s_4$ e $s_5$, livres no nível 1 ($b$ está em $s_3$). Apoio: os dois slots estão sobre $d$, e $2\geq\lceil 2/2\rceil$. Aqui $d$ não tem o topo totalmente livre, o que a pré-condição 2 original proibiria.
  $t=3$   $\mathit{mv}(a,c,4,3)$   $a$ tem o topo livre. Em $p=4$ ele sobrepõe $c$ e o slot $s_4$ do nível 2 está livre. Apoio: $s_4$ está sobre $c$, e $1\geq\lceil 1/2\rceil$.
  $t=4$   $\mathit{mv}(b,c,5,4)$   $b$ tem o topo livre. Em $p=5$ ele sobrepõe $c$ e o slot $s_5$ do nível 2 está livre. Apoio: $s_5$ está sobre $c$, e $1\geq\lceil 1/2\rceil$. Em $t=5$ o estado é $S_5$.

  : Plano manual da Situação 2, de $S_0$ até $S_5$.
:::

#### Por que 5 ações é o mínimo.

Como $a$ e $b$ começam sobre $c$ e $c$ só se move com o topo livre, os
dois precisam sair antes de $c$ se mover. Como terminam sobre $c$ em
$(4,1)$, cada um precisa de um segundo movimento depois que $c$ chegou
lá. Logo $a$ e $b$ se movem pelo menos duas vezes cada, e $c$ pelo menos
uma, o que dá $2+2+1=5$ ações. O bloco $d$ não precisa se mover.

#### Ordem parcial.

As metas $\varphi_1=on(c,d)$, $\varphi_2=on(a,c)$ e $\varphi_3=on(b,c)$
obedecem a $\varphi_1\prec_P\varphi_2$ e $\varphi_1\prec_P\varphi_3$,
pois $a$ e $b$ só ficam sobre $c$ depois que $c$ está em $(4,1)$. No
plano, $\varphi_1$ passa a valer em $t=3$, $\varphi_2$ em $t=4$ e
$\varphi_3$ em $t=5$. Entre $\varphi_2$ e $\varphi_3$ não há ordem: $b$
antes de $a$ também leva a $S_5$ com 5 ações.

### Codificação em CNF

As cláusulas do grupo 1 são as oito cláusulas unitárias de $S_0$ e as do
grupo 2 são as oito de $S_5$ com $T=5$, escritas acima. No script, o
cenário é configurado assim:

    INITIAL = {'a': (0,1), 'b': (1,1), 'c': (0,0), 'd': (3,0)}
    GOAL    = {'a': (4,2), 'b': (5,2), 'c': (4,1), 'd': (3,0)}
    HORIZON = 5

Pelo plano manual, o resultado esperado é `UNSATISFIABLE` para
$T=0,\dots,4$ e `SATISFIABLE` para $T=5$. Esse resultado deve ser
confirmado na execução descrita na Seção 6.

## Situação 3

### Estados inicial e meta

A Situação 3 parte do mesmo estado inicial $S_0$ da Situação 1 (bloco
$d$ em ponte sobre $a$ e $b$) e tem como meta o estado $S_7$: $a$ e $b$
lado a lado sobre $c$, e $d$ na mesa, em $p=3$. A
Figura [3](#fig:sit3-s0s7){reference-type="ref"
reference="fig:sit3-s0s7"} mostra os dois estados.

<figure id="fig:sit3-s0s7" data-latex-placement="H">

<figcaption>Estado inicial <span
class="math inline"><em>S</em><sub>0</sub></span> e meta <span
class="math inline"><em>S</em><sub>7</sub></span> da Situação
3.</figcaption>
</figure>

$$\begin{align*}
S_0 :\;& \mathit{at}(c,0) \wedge \mathit{lev}(c,0) \wedge \mathit{at}(a,3) \wedge \mathit{lev}(a,0)\\
       & \wedge\, \mathit{at}(b,5) \wedge \mathit{lev}(b,0) \wedge \mathit{at}(d,3) \wedge \mathit{lev}(d,1)\\
S_7 :\;& \mathit{at}(c,0) \wedge \mathit{lev}(c,0) \wedge \mathit{at}(a,0) \wedge \mathit{lev}(a,1)\\
       & \wedge\, \mathit{at}(b,1) \wedge \mathit{lev}(b,1) \wedge \mathit{at}(d,3) \wedge \mathit{lev}(d,0)
\end{align*}$$

::: center
  Estado   Relações $\mathit{on}$
  -------- ------------------------------------------------------------------------------------------------
  $S_0$    $\mathit{on}(c,T),\ \mathit{on}(a,T),\ \mathit{on}(b,T),\ \mathit{on}(d,a),\ \mathit{on}(d,b)$
  $S_7$    $\mathit{on}(c,T),\ \mathit{on}(d,T),\ \mathit{on}(a,c),\ \mathit{on}(b,c)$
:::

Conferência de consistência (restrições da Seção 2.3): em $S_0$ e $S_7$
todo bloco respeita $0\le p\le 6-\ell(b)$; não há dois blocos cobrindo o
mesmo slot no mesmo nível; $d$ em $S_0$ tem apoio em $s_3$ e $s_5$
($2\ge\lceil 3/2\rceil$), com $s_4$ vazio sob a ponte; em $S_7$, $a$ e
$b$ estão apoiados em $c$ ($1\ge\lceil 1/2\rceil$ cada).

### Plano manual

::: {#tab:plano-sit3}
  Passo   Ação                     Verificação
  ------- ------------------------ --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  $t=0$   $\mathit{move}(d,c,0)$   $d$ tem o topo livre. Destino: nível 1 sobre $c$, slots $s_0$--$s_2$ livres (e nada acima). Apoio em $s_0$ e $s_1$ ($2\ge 2$), sem precisar de $s_2$: é a ponte parcial. Libera $a$ e $b$.
  $t=1$   $\mathit{move}(a,b,5)$   $a$ livre. Sobrepõe $b$ em $s_5$; $s_5$ no nível 1 livre. Apoio em $b$. Tira $a$ do slot $s_3$ da mesa.
  $t=2$   $\mathit{move}(d,T,2)$   $d$ livre. Slots $s_2,s_3,s_4$ livres no nível 0 e nada acima deles ($a$ está em $s_5$). Libera o topo de $c$.
  $t=3$   $\mathit{move}(a,c,0)$   $a$ livre. Sobrepõe $c$ em $s_0$; $s_0$ no nível 1 livre. Apoio em $c$.
  $t=4$   $\mathit{move}(b,c,1)$   $b$ livre (pois $a$ saiu). Sobrepõe $c$ em $s_1$; $s_1$ no nível 1 livre. Apoio em $c$. Aqui $c$ já carrega $a$ e não tem o topo inteiro livre, o que a pré-condição 2 original proibiria (Seção 3.3).
  $t=5$   $\mathit{move}(d,T,3)$   $d$ livre. Slots $s_3,s_4,s_5$ livres no nível 0 ($a$ e $b$ já saíram da mesa). Em $t=6$ o estado é $S_7$.

  : Plano manual da Situação 3, de $S_0$ até $S_7$.
:::

<figure id="fig:plano-sit3" data-latex-placement="H">
<p><br />
</p>
<figcaption>Estados da Situação 3 ao longo do plano manual. Correspondem
às figuras <span
class="math inline"><em>S</em><sub>0</sub>, <em>S</em><sub>1</sub>, <em>S</em><sub>2</sub>, <em>S</em><sub>3</sub>, <em>S</em><sub>4</sub>, <em>S</em><sub>5</sub></span>
e <span class="math inline"><em>S</em><sub>7</sub></span> do
enunciado.</figcaption>
</figure>

#### Por que 6 ações é o mínimo.

$d$ não pode ir direto de $(3,1)$ para $(3,0)$, pois $a$ e $b$ ocupam os
slots $s_3$ e $s_5$ do nível 0 e só ficam livres depois que $d$ sai de
cima deles. Como o topo de $c$ precisa estar livre quando $a$ e $b$
forem para lá, $d$ não pode ficar sobre $c$; e para sair de cima de $c$
para a mesa em $p=2$, $a$ precisa antes deixar $s_3$. Isso dá três ações
para $d$, duas para $a$ e uma para $b$. A busca exaustiva (BFS) sobre as
mesmas regras do modelo confirma que não existe plano com menos de 6
ações.

#### Ordem parcial.

Com $\varphi_1(t)\equiv\mathit{lev}(d,0,t)$ e
$\varphi_2(t)\equiv\mathit{on}(a,c,t)$ (Seção 2.6), $\varphi_1$ vale
pela primeira vez em $t=3$ e $\varphi_2$ em $t=4$, logo
$\varphi_1\prec_P\varphi_2$ é respeitada com precedência estrita.

#### Observação sobre o enunciado.

Na figura da Situação 3, $S_5$ e $S_6$ são desenhados de forma idêntica.
O plano acima passa por $S_0,S_1,S_2,S_3,S_4,S_5$ e vai direto a $S_7$,
sem um estado repetido.

### Codificação em CNF

Os grupos 1 e 2 são as oito cláusulas unitárias de $S_0$ (em $t=0$) e as
oito de $S_7$ (em $t=H$), escritas acima. Com $H=6$ há $21\cdot 7=147$
variáveis $\mathit{at}$, $4\cdot 4\cdot 7=112$ de $\mathit{lev}$,
$4\cdot 7=28$ de $\mathit{clr}$ e $84\cdot 6=504$ de $\mathit{mv}$, num
total de 791, mais as auxiliares $\mathit{cov}$ e $o_0,\dots,o_6$ da
ordem parcial. No script:

    INITIAL = {'c': (0,0), 'a': (3,0), 'b': (5,0), 'd': (3,1)}
    GOAL    = {'c': (0,0), 'a': (0,1), 'b': (1,1), 'd': (3,0)}
    HORIZON = 6

Pelo plano manual, o resultado esperado é `UNSATISFIABLE` para
$H=0,\dots,5$ e `SATISFIABLE` para $H=6$, com ou sem a cláusula de ordem
parcial. Esse resultado deve ser confirmado na execução descrita na
Seção 6.

# Mapeamento: Descrição Formal para Código

Esta seção liga cada elemento da descrição formal (Seções 2 e 3) ao
trecho correspondente do código. O gerador de CNF é o `bw2cnf_var.py`,
adaptado do caso simples; a leitura do resultado é feita pelo
`interpretar.py`. Os nomes em fonte monoespaçada são funções,
dicionários ou variáveis do código.

## Domínio, estados e cenários

::: {#tab:map-dominio}
  Descrição formal                               Código (`bw2cnf_var.py`)
  ---------------------------------------------- -------------------------------------------------------------------------------------------------------------
  Blocos e comprimentos $\ell(b)$                `BLOCKS = {’a’:1, ’b’:1, ’c’:2, ’d’:3}`
  Pontos $X=\{0,\dots,6\}$ e 6 slots             `MAX_POINT = 6`
  Níveis $l\in\{0,1,2,3\}$                       `MAX_LEVEL = 3`
  Mesa $T$                                       `TABLE = ’T’` (evita confundir com o horizonte $T$)
  Posições válidas $0\le p\le 6-\ell(b)$         `valid_positions(b)`
  $\mathit{span}(b,p)=\{p,\dots,p+\ell(b)-1\}$   `span(b, p)`
  $\mathit{overlap}(b,p,y,q)$                    `spans_overlap(b1, p1, b2, p2)`
  Estado inicial e meta                          dicionários `INITIAL` e `GOAL`: bloco $\mapsto$ (ponto, nível)
  Horizonte $H$ (número de ações)                `HORIZON`; parâmetro `T` de `build()`
  Situações 1, 2 e 3                             dicionário `CENARIOS` (`sit1_sf1` a `sit1_sf4`, `sit2`, `sit3`); escolha em `CENARIO_PADRAO` ou `--cenario`
  Ordem parcial $\varphi_1\prec_P\varphi_2$      lista `ordem` de cada cenário, com pares $(\varphi_1,\varphi_2)$
  Pasta de saída por cenário                     dicionário `PASTA` (`situacao1/`, `situacao2/`, `situacao3/`)

  : Domínio e configuração: descrição formal $\to$ código.
:::

Cada cenário é descrito por `initial`, `goal`, `ordem` e `esperado`
(comprimento mínimo do plano, vindo do plano manual). Por exemplo, a
Situação 3 é:

    INITIAL = {'c': (0,0), 'a': (3,0), 'b': (5,0), 'd': (3,1)}
    GOAL    = {'c': (0,0), 'a': (0,1), 'b': (1,1), 'd': (3,0)}
    HORIZON = 6
    ordem   = [(('lev','d',0), ('on','a','c'))]   # d na mesa  <  a sobre c

## Variáveis proposicionais

Cada variável recebe um número inteiro por `new_var()`, que também
guarda o nome simbólico. Esse registro é o que vira o arquivo `.map`.

::: {#tab:map-vars}
  Descrição formal                         Código             Observação
  ---------------------------------------- ------------------ -----------------------------------------------
  $\mathit{at}(b,p,t)$                     `at[(b,p,t)]`      nome no mapa: `at(c,0,0)`
  $\mathit{lev}(b,l,t)$                    `lev[(b,l,t)]`     `lev(d,1,0)`
  $\mathit{clr}(b,t)$                      `clr[(b,t)]`       `clr(a,3)`
  $\mathit{mv}(b,y,p,t)$                   `mv[(b,y,p,t)]`    $t\in[0,H-1]$; `mv(d,c,0,0)`
  $\mathit{cov}(s,l,t)$                    `cov[(s,l,t)]`     auxiliar: slot $s$ coberto no nível $l$
  (parte de $\mathit{cov}$)                `cb[(b,s,l,t)]`    auxiliar: *o bloco $b$* cobre $s$ em $l$
  $\mathit{at}\wedge\mathit{lev}$          `pos(b,p,l,t)`     auxiliar, só na ordem parcial da Situação 2
  $o_t\leftrightarrow\mathit{on}(a,c,t)$   `o_on(b,y,t)`      auxiliar da ordem parcial
  $\mathit{on}(b,y,t)$                     *não codificada*   derivada em `derivar_on()` (`interpretar.py`)

  : Variáveis: descrição formal $\to$ código.
:::

## Grupos de cláusulas

::: {#tab:map-grupos}
  Grupo   Bloco em `build()`           Comentário
  ------- ---------------------------- --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  ---     definição de `cb` e `cov`    equivalências $\mathit{cov}(s,l,t)\leftrightarrow\bigvee_b \mathit{cb}(b,s,l,t)$ e $\mathit{cb}(b,s,l,t)\leftrightarrow\mathit{lev}(b,l,t)\wedge\bigvee_{p:\,s\in\mathit{span}(b,p)}\mathit{at}(b,p,t)$, usadas em 6 e 7
  1       `1. ESTADO INICIAL`          unitárias de `at` e `lev` em $t=0$
  2       `2. META`                    unitárias de `at` e `lev` em $t=H$
  3, 4    `3. UNICIDADE...`            ao menos um e no máximo um ponto; idem para nível
  5       `5. EXCLUSAO HORIZONTAL`     dois blocos no mesmo nível não cobrem o mesmo slot
  6       `6. ESTABILIDADE`            uma cláusula por subconjunto de $\ell(b)-\lceil\ell(b)/2\rceil+1$ slots do span
  7       `7. CLEAR`                   $\mathit{clr}(b,t)$ definida nos dois sentidos, em todo instante
  8       `8. PRE-CONDICOES...`        (a), (c), (d), (e) do texto; (b) removida (Seção 3.3); inclui o nível máximo e a cláusula do slot sob a ponte (marcada `3.4`)
  9       `...EFEITOS`                 `at`, `lev` em $t+1$ e $\neg\mathit{clr}(y,t+1)$
  10      `10. FRAME AXIOMS`           `at` e `lev` persistem se o bloco não se move
  11      `11. ACAO UNICA POR PASSO`   exatamente um `mv` por instante
  ---     `ORDEM PARCIAL`              $\varphi_2(t)\rightarrow\varphi_1(0)\vee\dots\vee\varphi_1(t-1)$

  : Grupos de cláusulas: Seção 3.2 $\to$ código.
:::

## O que muda em relação ao caso simples

- **Ação qualitativa.** A variável `mv` tem o destino simbólico $y$
  (bloco ou mesa) e o ponto $p$, em vez de nível e posição numéricos.

- **Sem a variável `on`.** A relação é derivada depois, o que reduz o
  número de variáveis e permite listar a ponte como dois apoios.

- **Variáveis auxiliares.** `cb` e `cov` permitem escrever estabilidade
  e clear como cláusulas curtas; `pos` e `o_on` servem à ordem parcial.

- **Ajustes do Manual** (Seção 2.7): sem $\mathit{clr}(y)$ como
  pré-condição; cláusula do slot sob a ponte; efeitos completos (apoio
  antigo e todos os apoios).

- **Nível máximo.** Se $y$ está no nível 3, $\mathit{mv}(b,y,p,t)$ é
  proibido, pois o destino seria o nível 4.

- **Cenário e saída.** O cenário é escolhido por nome, e os arquivos vão
  automaticamente para a pasta do cenário.

## Tamanho do CNF

::: {#tab:tamanho}
  Cenário                         $H$    Vars. base   Vars. auxiliares   Total de vars.   Cláusulas
  ------------------------------ ----- ------------ ------------------ ---------------- -----------
  Situação 1 ($S_0\to S_{f4}$)     4            541                605             1146       31390
  Situação 2 ($S_0\to S_5$)        5            666                737             1403       38839
  Situação 3 ($S_0\to S_7$)        6            791                847             1638       46534

  : Tamanho do CNF no menor horizonte satisfatível. As variáveis base
  ($\mathit{at}$, $\mathit{lev}$, $\mathit{clr}$, $\mathit{mv}$)
  coincidem com a contagem das Seções 3.1 e 4.
:::

# Execução Passo a Passo

O fluxo tem quatro passos. Os exemplos usam a Situação 3; para as
outras, troque o cenário.

#### 1. Configurar o cenário.

No topo do `bw2cnf_var.py`, escolha o cenário em `CENARIO_PADRAO`
(`’sit1_sf4’`, `’sit2’` ou `’sit3’`) ou passe `--cenario` na linha de
comando. Para a Situação 3, o script usa:

    INITIAL = {'c': (0,0), 'a': (3,0), 'b': (5,0), 'd': (3,1)}
    GOAL    = {'c': (0,0), 'a': (0,1), 'b': (1,1), 'd': (3,0)}
    HORIZON = 6

#### 2. Gerar o CNF e o mapa.

    python3 bw2cnf_var.py --cenario sit3

Saída:

    Pasta: situacao3/
    Gerado: 1638 variaveis, 46534 clausulas (base: 791; auxiliares: 847), horizonte T=6
    Arquivos: situacao3/trab01_blocos2SAT.cnf, situacao3/trab01_blocos2SAT.map

O `.cnf` está no formato DIMACS (primeira linha `p cnf 1638 46534`, uma
cláusula por linha terminada em `0`). O `.map` tem uma linha
`ID simbolo` por variável, por exemplo `4 at(a,3,0)`. O argumento
`--horizon` muda $H$ (`--cenario sit3 --horizon 5`); `--sem-ordem`
desliga a cláusula de ordem parcial.

#### 3. Executar o miniSAT.

    minisat situacao3/trab01_blocos2SAT.cnf situacao3/resultado3.txt

O miniSAT imprime estatísticas e a palavra `SATISFIABLE` (ou
`UNSATISFIABLE`), e grava no arquivo as linhas `SAT` e a lista de
inteiros. Ele relata menos cláusulas que o arquivo (32866 contra 46534)
porque simplifica o CNF antes de resolver. O tempo de resolução é
inferior a 0,1 s.

#### 4. Interpretar o resultado.

    python3 interpretar.py situacao3/resultado3.txt --verbose

    PLANO ENCONTRADO (6 acoes):
    1. t=0: mover bloco 'd' para CIMA de 'c' em p=0
    2. t=1: mover bloco 'a' para CIMA de 'b' em p=5
    3. t=2: mover bloco 'd' para a MESA em p=2
    4. t=3: mover bloco 'a' para CIMA de 'c' em p=0
    5. t=4: mover bloco 'b' para CIMA de 'c' em p=1
    6. t=5: mover bloco 'd' para a MESA em p=3

    ESTADO FINAL (t=6):
      a: ponto inicial p=0, nivel l=1
      b: ponto inicial p=1, nivel l=1
      c: ponto inicial p=0, nivel l=0
      d: ponto inicial p=3, nivel l=0

    RELACOES 'on' em t=6:
      a esta sobre: c
      b esta sobre: c
      c esta na MESA
      d esta na MESA

Sem `--map`, o `interpretar.py` usa o `trab01_blocos2SAT.map` da mesma
pasta do resultado. A opção `--verbose` também imprime a evolução do
estado em cada instante.

## Horizonte crescente

Para achar o plano mínimo, o horizonte é aumentado ($H=0,1,2,\dots$) até
o primeiro `SATISFIABLE`. O script `rodar_cenarios.py` faz esse laço:
para cada $H$ gera o CNF, chama o miniSAT, e ao encontrar o primeiro SAT
salva `.cnf`, `.map` e `resultadoN.txt` na pasta do cenário.

    python3 rodar_cenarios.py              # Situacoes 1 (Sf4), 2 e 3
    python3 rodar_cenarios.py --todos      # inclui Sf1, Sf2 e Sf3

::: {#tab:horizonte}
  Cenário                 UNSAT em         SAT em    Variáveis   Cláusulas  Ações do plano
  ----------------------- --------------- -------- ----------- ----------- ----------------
  Situação 1 ($S_{f4}$)   $H=0,\dots,3$    $H=4$          1146       31390        4
  Situação 2 ($S_5$)      $H=0,\dots,4$    $H=5$          1403       38839        5
  Situação 3 ($S_7$)      $H=0,\dots,5$    $H=6$          1638       46534        6
  Situação 1 ($S_{f1}$)   $H=0,\dots,8$    $H=9$          2366       68940        9
  Situação 1 ($S_{f2}$)   $H=0,\dots,9$    $H=10$         2611       76481        10
  Situação 1 ($S_{f3}$)   $H=0,\dots,9$    $H=10$         2611       76481        10

  : Resultado do horizonte crescente. Em cada linha, vale o menor $H$
  satisfatível.
:::

Os resultados são exatamente os previstos pelos planos manuais (Seção 4)
e pela busca exaustiva sobre as mesmas regras (`busca_exaustiva.py`): 4,
5 e 6 ações para as três situações, e 9, 10 e 10 para $S_{f1}$, $S_{f2}$
e $S_{f3}$.

## Verificação independente

O `busca_exaustiva.py` implementa as pré-condições P1--P7 como um
simulador de estados, sem SAT. Ele serve a dois fins: achar por BFS o
plano mínimo de cada cenário e conferir, passo a passo, se um plano é
legal e atinge a meta. O `rodar_cenarios.py` aplica essa verificação a
todo plano devolvido pelo SAT, e todos passaram. Os planos manuais do
relatório (Seções 4.1.2, 4.2.2 e 4.3.2) também são legais pelo mesmo
simulador.

# Interpretação da Saída do SAT Solver

## O miniSAT não conhece nomes simbólicos

O miniSAT é um resolvedor puramente booleano. Para um CNF satisfatível,
grava a palavra `SAT` e, na linha seguinte, uma lista de inteiros
terminada em `0`. Um inteiro positivo $v$ significa que a variável $v$ é
verdadeira; um negativo $-v$, que é falsa. Por exemplo, o resultado da
Situação 3 começa com:

    SAT
    -1 -2 -3 4 -5 -6 7 -8 -9 -10 -11 -12 -13 -14 -15 -16 17 18 ...

Aqui os valores verdadeiros $4$, $7$, $17$ e $18$ só ganham sentido com
o `.map`: `4 at(a,3,0)` diz que $a$ começa no ponto 3 em $t=0$. Em toda
a saída da Situação 3, 182 das 1638 variáveis são verdadeiras.

## Da saída numérica ao plano em português

O `interpretar.py` executa três passos:

1.  **Leitura do mapa** (`ler_mapa`): associa cada ID ao seu símbolo.

2.  **Filtragem** (`ler_resultado`): mantém apenas os literais
    positivos. Se a primeira linha for `UNSAT`, avisa que não há plano e
    termina.

3.  **Ordenação temporal** (`acoes`, `frase`): fica só com as variáveis
    `mv(b,y,p,t)` verdadeiras, ordena por $t$ e traduz cada uma em uma
    frase.

Na Situação 3, as seis variáveis `mv` verdadeiras são:

::: {#tab:mv-verdadeiras}
     ID Símbolo no `.map`   Frase
  ----- ------------------- -------------------------------------
    364 `mv(d,c,0,0)`       mover $d$ para cima de $c$ em $p=0$
    377 `mv(a,b,5,1)`       mover $a$ para cima de $b$ em $p=5$
    538 `mv(d,T,2,2)`       mover $d$ para a mesa em $p=2$
    546 `mv(a,c,0,3)`       mover $a$ para cima de $c$ em $p=0$
    655 `mv(b,c,1,4)`       mover $b$ para cima de $c$ em $p=1$
    791 `mv(d,T,3,5)`       mover $d$ para a mesa em $p=3$

  : Variáveis `mv` verdadeiras na Situação 3 e o plano que elas
  representam.
:::

#### Conferências de sanidade.

A contagem das variáveis verdadeiras por família confirma as restrições
do CNF: há 28 $\mathit{at}$ e 28 $\mathit{lev}$ verdadeiras ($4$ blocos
$\times$ $7$ instantes, pela unicidade), exatamente 6 $\mathit{mv}$ (uma
por passo, pelo grupo 11), 19 $\mathit{clr}$, 49 $\mathit{cov}$, 49
$\mathit{cb}$ e 3 $o\_\mathit{on}$ (auxiliares).

## Derivação de $\mathit{on}$

A relação $\mathit{on}$ não é codificada. O `interpretar.py` a
reconstrói em `derivar_on` a partir de $\mathit{at}$, $\mathit{lev}$ e
da sobreposição de spans, como na Seção 2.2:
$$\mathit{on}(b,y,t)\leftrightarrow\exists p,q,l.\;
\mathit{at}(b,p,t)\wedge\mathit{at}(y,q,t)\wedge\mathit{lev}(b,l,t)\wedge
\mathit{lev}(y,l-1,t)\wedge\mathit{overlap}(b,p,y,q).$$ Na prática, para
cada bloco $b$ no estado de $t$:

- se $\mathit{lev}(b)=0$, então $\mathit{on}(b,T,t)$ (sobre a mesa);

- se $\mathit{lev}(b)=l>0$, procura todos os blocos $y$ com
  $\mathit{lev}(y)=l-1$ cujo span sobrepõe o de $b$. Pode haver mais de
  um: é a *ponte*.

Como o estado de cada $t$ é reconstruído de $\mathit{at}$ e
$\mathit{lev}$ (`estados_por_tempo`), a mesma função vale para qualquer
instante. Na Situação 3:

::: {#tab:on-derivado}
   $t$  Estado $(p,l)$                           Relações $\mathit{on}$ derivadas
  ----- ---------------------------------------- ----------------------------------------------------
    0   $a(3,0)$, $b(5,0)$, $c(0,0)$, $d(3,1)$   $d$ sobre $a$ e $b$ (ponte); $a$, $b$, $c$ na mesa
    1   $a(3,0)$, $b(5,0)$, $c(0,0)$, $d(0,1)$   $d$ sobre $c$; $a$, $b$, $c$ na mesa
    6   $a(0,1)$, $b(1,1)$, $c(0,0)$, $d(3,0)$   $a$ e $b$ sobre $c$; $c$ e $d$ na mesa

  : Relações $\mathit{on}$ derivadas do estado reconstruído.
:::

A opção `--verbose` imprime as relações $\mathit{on}$ do estado final e
a evolução $(p,l)$ de cada bloco em todo $t$. A relação do estado
inicial (a ponte de $d$ sobre $a$ e $b$) é obtida chamando `derivar_on`
sobre o estado de $t=0$.

## Caso UNSATISFIABLE

Se o horizonte é menor que o comprimento mínimo do plano, o miniSAT
responde `UNSATISFIABLE` e grava só `UNSAT` no arquivo. O
`interpretar.py` avisa e termina com código de saída 1:

    UNSATISFIABLE: nao existe plano com esse horizonte.

Isso é o resultado esperado para $H<$ mínimo (por exemplo, $H=5$ na
Situação 3) e é o que prova que o plano do menor $H$ satisfatível é
mínimo.

## Regra de ouro

**Sem o arquivo `.map`, a saída numérica do miniSAT é apenas uma lista
de inteiros sem significado para o domínio.** Além disso, o mapa precisa
ser o da *mesma execução*: a numeração depende do cenário e do
horizonte, pois as variáveis são criadas na ordem de $t$, bloco e
posição. Por isso cada pasta `situacaoN/` guarda o par `.cnf`/`.map`
junto ao `resultadoN.txt`.

Como demonstração, interpretar o resultado da Situação 3 com o mapa da
Situação 2 não dá erro, mas devolve um plano sem sentido:

    PLANO ENCONTRADO (16 acoes):
    1. t=0: mover bloco 'a' para a MESA em p=0
    2. t=0: mover bloco 'a' para a MESA em p=3
    3. t=0: mover bloco 'a' para a MESA em p=4
    ...

São várias ações no mesmo instante $t=0$, o que o grupo 11 proíbe. Esse
tipo de saída indica mapa trocado.

## Comparação com os planos manuais

::: {#tab:comparacao}
  Cenário                  Ações (SAT)   Ações (manual)  Comparação
  ----------------------- ------------- ---------------- ----------------------------------------------------
  Situação 1 ($S_{f4}$)         4              4         plano idêntico ao manual
  Situação 2 ($S_5$)            5              5         planos diferentes, ambos legais e mínimos (abaixo)
  Situação 3 ($S_7$)            6              6         plano idêntico ao manual

  : Planos do SAT contra os planos manuais.
:::

Na Situação 2, o SAT escolheu um caminho diferente do manual. O manual
(Seção 4.2.2) tira $a$ de cima de $c$ colocando-o na mesa em $p=2$ e põe
$b$ sobre $d$; o SAT põe $a$ sobre $d$ em $p=3$ e leva $b$ à mesa em
$p=2$. Daí em diante os planos coincidem: $c$ sobe em $d$ em $p=4$,
depois $a$ e $b$ sobem em $c$. Há, portanto, mais de um plano mínimo, e
o SAT devolve um deles. Para os dois, a ordem parcial (primeiro $c$ em
$(4,1)$, depois $a$ e $b$ sobre $c$) é respeitada.
