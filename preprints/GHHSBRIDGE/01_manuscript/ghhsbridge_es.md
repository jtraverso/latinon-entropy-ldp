# Las representaciones por núcleos y por medidas de los Latinons coinciden: una formalización en Lean

Juan Pablo Traverso Gianini

Preprint 1.0 — 16 de noviembre de 2026.

DOI: https://doi.org/10.5281/zenodo.24293531.

Repositorio: https://github.com/jtraverso/latinon-entropy-ldp.

## Resumen

En [2] establecimos un teorema de conteo para cuadrados latinos con densidades de patrones prescritas, como confirmación de la conjetura 12.4 de Garbe, Hancock, Hladký y Sharifzadeh [1]. Sin embargo, mientras que [1] formula los Latinons mediante núcleos de Markov, la formalización en Lean de [2] trabaja con medidas en el cubo unidad, de modo que la equivalencia entre los dos marcos quedó demostrada solo en papel. Aquí formalizamos esa equivalencia en Lean: mostramos que ambas representaciones dan los mismos Latinons, la misma distancia de corte, las mismas densidades de patrones y la misma entropía, y completamos así la demostración en Lean de la conjetura 12.4 con las definiciones de [1] sobre el espacio base $[0,1]$ (con la entropía entendida como el negativo de la entropía relativa).

## 1. Introducción

Garbe, Hancock, Hladký y Sharifzadeh [1] introdujeron los Latinons, que son los objetos límite de los cuadrados latinos, y conjeturaron que la entropía de un Latinon determina cuántos cuadrados latinos hay cerca de él. Su conjetura 12.4 precisa esta idea para cuadrados con densidades de patrones prescritas. En [2] demostramos un teorema de conteo con esa misma forma [2, teorema 2.2] y afirmamos que confirma la conjetura.

Entre ese teorema y la conjetura hay una diferencia de lenguaje. En [1] un Latinon es un núcleo: a cada par formado por una fila y una columna le asigna una distribución de probabilidad sobre los símbolos. En [2] un Latinon es una medida en el cubo unidad cuyas marginales de dimensión dos son uniformes. Los teoremas de [2] están demostrados, y comprobados en Lean, para medidas. Que digan lo mismo sobre núcleos es el contenido de [2, proposición 2.3], que se demostró en papel pero no en Lean. La formalización de [2] se queda así a un paso de la conjetura tal como fue enunciada originalmente.

Aquí cerramos esa brecha: mostramos que los Latinons de núcleo y los Latinons de medida están en correspondencia canónica salvo conjuntos nulos (sección 2), y que esta correspondencia conserva la distancia de corte (sección 3), las densidades de patrones (sección 4) y la entropía (sección 5). La conjetura 12.4 solo involucra estas cantidades, así que se sigue de [2, teorema 2.2]; en la sección 6 la enunciamos con las definiciones de [1]. Todos los resultados están demostrados en Lean, y la sección 7 indica las declaraciones correspondientes.

Siguiendo a [2], adoptamos dos convenciones en todo el texto. Primero, fijamos el espacio base $I=[0,1]$ con la medida de Lebesgue $\lambda$; aunque [1] admite cualquier espacio de probabilidad separable y sin átomos, todos ellos son isomorfos a $(I,\lambda)$ salvo conjuntos nulos [1, sección 2.3] (un isomorfismo que damos por conocido y no formalizamos). Segundo, definimos la entropía como el negativo de la entropía relativa, con el signo opuesto al de la integral $\int g\log g$ impresa en [1, sección 12.2], que de otro modo predeciría, cerca de un Latinon no uniforme, más cuadrados latinos de los que existen.

## 2. Núcleos y medidas

De un núcleo se obtiene una medida integrando, y de una medida se obtiene un núcleo condicionando respecto de la fila y la columna. Mostramos que estas dos operaciones llevan Latinons de un tipo a Latinons del otro, y que cada una deshace la otra.

Un Latinon de medida, como en [2], es un par $(\nu,f)$ donde $\nu$ es una medida de probabilidad en $(I\times I)\times I$ cuyas tres marginales de dos coordenadas son $\lambda^2$, y $f:I\to I$ preserva $\lambda$. Las coordenadas son fila, columna y símbolo, y $f$ da el orden de las filas y de las columnas.

Un Latinon de núcleo, como en [1, definición 3.5], es un par $(K,f)$ donde $K$ es un núcleo de Markov de $I\times I$ en $I$, $f:I\to I$ preserva $\lambda$, y se cumplen las siguientes condiciones por filas y por columnas. Para una fila $x$ sea $\mu^1_x$ la imagen de $\lambda\otimes K(x,\cdot)$ por $(y,z)\mapsto(f(y),z)$, y para una columna $y$ sea $\mu^2_y$ la imagen de $\lambda\otimes K(\cdot,y)$ por $(x,z)\mapsto(f(x),z)$, de modo que

$$
\mu^1_x(S\times T)=\int_{f^{-1}(S)}K(x,y)(T)\,dy,\qquad
\mu^2_y(S\times T)=\int_{f^{-1}(S)}K(x,y)(T)\,dx.\tag{2.1}
$$

Las condiciones piden que $\mu^1_x$ sea un permutón para casi todo $x$ y que $\mu^2_y$ sea un permutón para casi todo $y$; es decir, que las dos marginales de estas medidas sean $\lambda$.

Un núcleo $K$ define la medida

$$
\nu_K=\lambda^2\otimes K,\qquad
\nu_K(S\times T\times U)=\int_{S\times T}K(x,y)(U)\,d\lambda^2(x,y),\tag{2.2}
$$

y una medida $\nu$ en el cubo cuya marginal fila–columna es $\lambda^2$ define por desintegración un núcleo $K_\nu$, la distribución condicional del símbolo dadas la fila y la columna, que cumple $\lambda^2\otimes K_\nu=\nu$.

**Teorema 2.1 (equivalencia de las dos descripciones).** Sean $(K,f)$ un Latinon de núcleo y $(\nu,f)$ un Latinon de medida.

(a) $(\nu_K,f)$ es un Latinon de medida.

(b) $(K_\nu,f)$ es un Latinon de núcleo.

(c) Al pasar de $\nu$ a su núcleo y volver se recupera $\nu$.

(d) Al pasar de $K$ a su medida y volver se obtiene un núcleo que coincide con $K$ para $\lambda^2$-casi todo $(x,y)$. Dos Latinons de núcleo con el mismo mapa de orden cuyos núcleos coinciden $\lambda^2$-casi en todas partes tienen la misma medida.

Así, los Latinons de medida corresponden a los Latinons de núcleo salvo conjuntos nulos, que es como se identifican los Latinons en [1].

*Demostración.* La condición por filas dice que el núcleo promedia $\lambda$ a lo largo de casi toda fila, mientras que la uniformidad de la marginal fila–símbolo es la versión integrada de esa misma identidad.

*(a)* La marginal fila–columna de $\nu_K$ es $\lambda^2$ porque cada $K(x,y)$ es una medida de probabilidad. Por (2.1) con $S=I$, la segunda marginal de $\mu^1_x$ es $U\mapsto\int K(x,y)(U)\,dy$, y la condición por filas dice que vale $\lambda(U)$ para casi todo $x$. Integrando sobre un conjunto $S$ de filas y usando (2.2) se obtiene $\nu_K(S\times I\times U)=\lambda(S)\lambda(U)$. La marginal columna–símbolo se obtiene igual.

*(b)* La primera marginal de $\mu^1_x$ es la imagen de $\lambda$ por $f$, que es $\lambda$. Para la segunda, sea $R(x)=\int K_\nu(x,y)\,dy$ el promedio del núcleo a lo largo de la fila $x$. Por (2.2) y la marginal fila–símbolo uniforme de $\nu$,

$$
(\lambda\otimes R)(S\times U)=\nu(S\times I\times U)=\lambda(S)\lambda(U),
$$

así que $\lambda\otimes R=\lambda\otimes\lambda$. Una medida en $I^2$ determina sus distribuciones condicionales salvo un conjunto nulo, luego $R(x)=\lambda$ para casi todo $x$. Esta es la condición por filas, y la condición por columnas se obtiene igual.

*(c)* Es la identidad $\lambda^2\otimes K_\nu=\nu$.

*(d)* Tanto $K$ como $K_{\nu_K}$ son distribuciones condicionales de $\nu_K$ dadas la fila y la columna, así que coinciden casi en todas partes. Núcleos que coinciden casi en todas partes tienen la misma integral (2.2). $\square$

En [2], el intercambio de cuantificadores de (b), de «para todo $U$, para casi todo $x$» a «para casi todo $x$, para todo $U$», se obtuvo probando con intervalos de extremos racionales; en Lean es más limpio reunir los promedios por filas en el núcleo de Markov $R$ y apelar a la unicidad, casi en todas partes, de las distribuciones condicionales.

## 3. La distancia de corte

Tanto [1] como [2] definen la distancia de corte tomando el ínfimo, sobre todos los reetiquetados de filas y columnas que preservan la medida, de la discrepancia entre los mapas de orden más la discrepancia, caja por caja, entre las distribuciones de símbolos. La única diferencia formal es que [1] expresa la discrepancia de símbolos con núcleos y [2] con medidas, dos cantidades que coinciden por (2.2).

Para $X:I^2\to\mathbb R$ medible y acotada sea $\|X\|_\square=\sup_{S,T}|\int_{S\times T}X|$, con $S,T\subseteq I$ medibles [1, sección 2.4.1]. Para un mapa de orden $f$ sea $O^f(x,y)=\mathbf 1[f(x)<f(y)]$ [1, definición 4.2]. Para núcleos $K,K'$ sea

$$
\|K-K'\|_{\boxtimes}=\sup_{S,T,V}\left|\int_{S\times T}\bigl(K(x,y)(V)-K'(x,y)(V)\bigr)\,dx\,dy\right|,\tag{3.1}
$$

donde $V$ recorre los intervalos de $I$ [1, definición 4.1]. Un reetiquetado es un par de biyecciones medibles $\phi,\psi:I\to I$ que preservan $\lambda$ y tienen inversa medible; actúa por $K^{\phi,\psi}(x,y)=K(\phi(x),\psi(y))$. La distancia de corte de [1, definición 4.3] entre $L_1=(K,f)$ y $L_2=(K',g)$ es

$$
\delta_{\boxtimes}(L_1,L_2)=\inf_{\phi,\psi}\Bigl(\|O^f-O^{g\circ\phi}\|_\square+\|O^f-O^{g\circ\psi}\|_\square+\|K-K'^{\phi,\psi}\|_{\boxtimes}\Bigr).\tag{3.2}
$$

Sea $\delta$ la distancia (2.1) de [2] entre Latinons de medida.

**Teorema 3.1 (distancia).** Para Latinons de núcleo $L_1=(K,f)$ y $L_2=(K',g)$, $\delta_{\boxtimes}(L_1,L_2)=\delta\bigl((\nu_K,f),(\nu_{K'},g)\bigr)$. En particular, $\delta_{\boxtimes}$ no cambia si un núcleo se modifica en un conjunto $\lambda^2$-nulo.

*Demostración.* Fijemos un reetiquetado $(\phi,\psi)$. La integral de $O^f$ sobre $S\times T$ es $\lambda^2((S\times T)\cap\{f(x)<f(y)\})$, que es como [2] escribe los términos de orden. Para el término de símbolos, (2.2) da $\int_{S\times T}K(x,y)(V)=\nu_K(S\times T\times V)$, y como $\phi\times\psi$ preserva $\lambda^2$, un cambio de variables da

$$
\int_{S\times T}K'(\phi(x),\psi(y))(V)\,dx\,dy=\nu_{K'}\bigl(\phi(S)\times\psi(T)\times V\bigr).\tag{3.3}
$$

El lado derecho es la medida reetiquetada de [2] evaluada en $S\times T\times V$. Por tanto los tres términos coinciden para cada reetiquetado, y los ínfimos coinciden. La última afirmación se sigue del teorema 2.1(d). $\square$

## 4. Densidades de patrones

La densidad de un patrón es la probabilidad de verlo cuando se eligen al azar $k$ filas y $\ell$ columnas y cada una de las $k\ell$ celdas recibe un símbolo sorteado con el núcleo. En [1] los símbolos se sortean con el núcleo dado $K$, mientras que en [2] se sortean con el núcleo desintegrado $K_\nu$; por el teorema 2.1 los dos coinciden $\lambda^2$-casi en todas partes, y eso basta porque cada celda $(x_i,y_j)$ de una configuración al azar se distribuye uniformemente en $I^2$.

Un patrón $A\in\mathcal R(k,\ell)$ es una matriz $k\times\ell$ de rangos distintos, y $\mathcal R_A([0,1])$ es el conjunto de las matrices reales con el mismo orden relativo [1, sección 3]. Escribimos $I^k_{<f}$ para las $k$-tuplas $x$ con $f(x_1)<\dots<f(x_k)$. La densidad de [1, definición 3.7] es

$$
t(A,(K,f))=k!\,\ell!\int_{x\in I^k_{<f}}\int_{y\in I^\ell_{<f}}\Bigl(\bigotimes_{(i,j)}K(x_i,y_j)\Bigr)\bigl(\mathcal R_A([0,1])\bigr)\,dy\,dx,\tag{4.1}
$$

y la densidad $d_A(\nu,f)$ de [2] es la misma expresión con $K_\nu$ en lugar de $K$.

**Teorema 4.1 (densidades de patrones).** Para un Latinon de núcleo $(K,f)$ y todo patrón $A$, $t(A,(K,f))=d_A(\nu_K,f)$.

*Demostración.* Por el teorema 2.1(d), $K$ y $K_{\nu_K}$ coinciden fuera de un conjunto $\lambda^2$-nulo $N$. Para cada celda $(i,j)$, el punto $(x_i,y_j)$ de una configuración al azar $(x,y)$ tiene distribución $\lambda^2$, así que cae en $N$ con probabilidad cero. Como hay un número finito de celdas, para casi toda configuración todos los factores de (4.1) son los mismos con los dos núcleos, y las integrales coinciden. $\square$

## 5. Entropía

En [1] la entropía de un Latinon se calcula celda por celda: se toma la entropía de la distribución de símbolos $K(x,y)$ y se promedia sobre filas y columnas. En [2] es la entropía de la medida $\nu$ en el cubo. Las dos coinciden por la regla de la cadena de la entropía relativa.

Sea $\operatorname{KL}$ la entropía relativa, con valores en $[0,\infty]$. Si una medida de probabilidad $\mu$ en $I$ tiene densidad $g$ respecto de $\lambda$, entonces $\operatorname{KL}(\mu\Vert\lambda)=\int g\log g\,d\lambda$, que puede ser infinito; si no tiene densidad, $\operatorname{KL}(\mu\Vert\lambda)=\infty$. Para un Latinon de núcleo $L=(K,f)$ ponemos

$$
\mathcal I_{\boxtimes}(L)=\int_{I^2}\operatorname{KL}\bigl(K(x,y)\Vert\lambda\bigr)\,d\lambda^2(x,y)\in[0,\infty],\qquad
\operatorname{Ent}_{\boxtimes}(L)=-\mathcal I_{\boxtimes}(L).\tag{5.1}
$$

Cuando el núcleo tiene densidades $g(x,y,\cdot)$, la primera cantidad es la integral $\int g\log g$ sobre el cubo que aparece en [1, sección 12.2]. La entropía de un Latinon de medida en [2] es $\operatorname{Ent}(\nu,f)=-\operatorname{KL}(\nu\Vert\lambda^3)$.

**Lema 5.1 (regla de la cadena condicional).** Sea $\mu$ una medida finita en un espacio medible $X$, y sean $\kappa,\eta$ núcleos de Markov de $X$ en un espacio medible $Y$. Supongamos que $X$ es numerable o que $Y$ es numerablemente generado. Entonces

$$
\operatorname{KL}(\mu\otimes\kappa\Vert\mu\otimes\eta)=\int_X\operatorname{KL}(\kappa(a)\Vert\eta(a))\,d\mu(a)\tag{5.2}
$$

en $[0,\infty]$, donde la integral es la integral inferior de Lebesgue.

*Demostración.* Supongamos primero que $\kappa(a)$ tiene densidad respecto de $\eta(a)$ para $\mu$-casi todo $a$. Bajo la hipótesis sobre los espacios, estas densidades se pueden elegir como una sola función conjuntamente medible $\rho(a,b)$, y entonces $\rho$ es una densidad de $\mu\otimes\kappa$ respecto de $\mu\otimes\eta$. La entropía relativa es la integral de $\varphi(\rho)$ respecto de la medida de referencia, con $\varphi(t)=t\log t-t+1\ge0$, y (5.2) es el teorema de Tonelli aplicado a $\varphi(\rho)$.

En caso contrario, el conjunto de los puntos $a$ en los que $\kappa(a)$ no tiene densidad respecto de $\eta(a)$ es medible y tiene $\mu$-medida positiva. El integrando de (5.2) vale $\infty$ en ese conjunto, así que el lado derecho es $\infty$. El lado izquierdo también es $\infty$, porque entonces $\mu\otimes\kappa$ no tiene densidad respecto de $\mu\otimes\eta$. $\square$

Aunque el lema 5.1 es estándar, la versión de Mathlib [3] que usamos solo ofrece la regla de la cadena no condicional y deja la forma condicional como tarea pendiente; por eso incluimos una demostración. Formular (5.2) con integrales inferiores de Lebesgue de funciones no negativas evita cualquier hipótesis auxiliar de integrabilidad.

**Teorema 5.2 (entropía).** Para un Latinon de núcleo $L=(K,f)$, $\mathcal I_{\boxtimes}(L)=\operatorname{KL}(\nu_K\Vert\lambda^3)$. Por tanto $\operatorname{Ent}_{\boxtimes}(L)=\operatorname{Ent}(\nu_K,f)$, también cuando ambas valen $-\infty$.

*Demostración.* Se aplica el lema 5.1 con $\mu=\lambda^2$, $\kappa=K$ y $\eta$ el núcleo constante de valor $\lambda$, para los cuales $\mu\otimes\kappa=\nu_K$ y $\mu\otimes\eta=\lambda^3$. $\square$

## 6. La conjetura 12.4

La conjetura 12.4 de [1] dice lo siguiente. Sean $A_i$ un número finito de patrones y $a_i\in[0,1]$, y sea $\alpha$ el supremo de la entropía sobre todos los Latinons $L$ con $t(A_i,L)=a_i$ para cada $i$. Entonces para cada $\varepsilon>0$ existen $\delta>0$ y $n_0$ tales que, para cada $n>n_0$, el número $N$ de cuadrados latinos de orden $n$ cuyas densidades cumplen $t(A_i,\cdot)=a_i\pm\delta$ para cada $i$ satisface

$$
\frac1{n^2}\log\frac{N}{(n/e^2)^{n^2}}=\alpha\pm\varepsilon.\tag{6.1}
$$

Por las secciones 2–5, cada cantidad de este enunciado se conserva al pasar de núcleos a medidas, lo que traduce la conjetura 12.4 directamente en [2, teorema 2.2]. Como [1] no precisa cómo interpretar (6.1) cuando $\alpha=-\infty$ (cuando ningún Latinon tiene las densidades prescritas, o todos los que las tienen son de entropía $-\infty$), leemos que el lado izquierdo diverge a $-\infty$ y enunciamos este caso degenerado aparte, en el teorema 6.3.

Sean $(A_j)_{j\in J}$ una familia finita de patrones y $a\in\mathbb R^J$. Sea $\alpha$ el supremo de $\operatorname{Ent}_{\boxtimes}(L)$ sobre los Latinons de núcleo $L$ con $t(A_j,L)=a_j$ para todo $j$, que es $-\infty$ si no hay ninguno. Sea $N_n(\delta)$ el número de cuadrados latinos $Q$ de orden $n$ con $|t(A_j,Q)-a_j|\le\delta$ para todo $j$, donde $t(A_j,Q)$ es la densidad de [1, definición 3.3], que es también la que se usa en [2]. Por último, sea $\mathcal J(a)$ el ínfimo de $\operatorname{KL}(\nu\Vert\lambda^3)$ sobre los Latinons de medida con densidades de patrones $a$, como en [2, (2.6)].

**Lema 6.1.** $\alpha=-\mathcal J(a)$.

*Demostración.* Por los teoremas 4.1 y 5.2, un Latinon de núcleo con densidades $a$ da un Latinon de medida con densidades $a$ y la misma entropía, así que $\alpha\le-\mathcal J(a)$. Recíprocamente, si algún Latinon de medida tiene densidades $a$, el ínfimo $\mathcal J(a)$ se alcanza [2, sección 2], y por el teorema 2.1 el minimizador proviene de un Latinon de núcleo con las mismas densidades y entropía $-\mathcal J(a)$. Si ninguno tiene densidades $a$, ambos lados valen $-\infty$. $\square$

**Teorema 6.2 (conjetura 12.4, caso finito).** Supongamos $\alpha>-\infty$. Para todo $\varepsilon>0$ existen $\delta>0$ y $n_0$ tales que, para todo $n\ge n_0$, $N_n(\delta)>0$ y

$$
\left|\frac1{n^2}\log\frac{N_n(\delta)}{(n/e^2)^{n^2}}-\alpha\right|\le\varepsilon.\tag{6.2}
$$

*Demostración.* Por el lema 6.1, $\mathcal J(a)$ es finito e igual a $-\alpha$. El teorema 2.2 de [2] da $\delta$ y $n_0$ con $N_n(\delta)>0$ y $|n^{-2}\log N_n(\delta)-(\log n-2)+\mathcal J(a)|\le\varepsilon$ para $n\ge n_0$. Esto es (6.2), porque $n^{-2}\log\bigl(N/(n/e^2)^{n^2}\bigr)=n^{-2}\log N-(\log n-2)$. $\square$

**Teorema 6.3 (conjetura 12.4, caso $\alpha=-\infty$).** Supongamos $\alpha=-\infty$. Para todo $t\in\mathbb R$ existen $\delta>0$ y $n_0$ tales que, para todo $n\ge n_0$,

$$
N_n(\delta)\le\exp\bigl\{n^2(\log n-2-t)\bigr\}.\tag{6.3}
$$

Dicho de otro modo, para $n\ge n_0$ o bien $N_n(\delta)=0$, o bien el lado izquierdo de (6.1) es a lo sumo $-t$.

*Demostración.* Por el lema 6.1, $\mathcal J(a)=\infty$. Si ningún Latinon de medida tiene densidades $a$, el teorema 2.2 de [2] muestra que $N_n(\delta)=0$ para un $\delta$ adecuado y todo $n$ grande. En otro caso, su cota superior para tasa infinita da (6.3). $\square$

## 7. El desarrollo en Lean

Todos los resultados de esta nota están formalizados en Lean 4.35.0, en siete módulos con raíz `GHHSBridge`, que extienden la formalización de [2] (`Latinon_Lean_v1.0.zip`) sobre un commit fijo de Mathlib [3] (registrado en el repositorio). El desarrollo no contiene ningún `sorry` ni axiomas propios, y todas las declaraciones principales dependen únicamente de los axiomas fundacionales estándar `propext`, `Classical.choice` y `Quot.sound`. Las fuentes, el registro de compilación y el informe de axiomas están en `preprints/GHHSBRIDGE`, en el repositorio indicado en la portada.

Los resultados numerados corresponden a las siguientes declaraciones, todas en el espacio de nombres `GHHSBridge`.

| Resultado | Declaración Lean | Módulo |
|------|------------------|------|
| Teorema 2.1(a) | `GHHSLatinon.toLatinonMeasure` | `ToMeasure` |
| Teorema 2.1(b) | `ofLatinonMeasure` | `OfMeasure` |
| Teorema 2.1(c) | `toLatinonMeasure_ofLatinonMeasure` | `OfMeasure` |
| Teorema 2.1(d) | `ofLatinonMeasure_toLatinonMeasure_kernel`, `toLatinonMeasure_eq_of_ae` | `OfMeasure`, `Distance` |
| Teorema 3.1 | `ghhsCutDistance_eq`, `ghhsCutDistance_congr_ae` | `Distance` |
| Teorema 4.1 | `ghhsPatternDensity_eq` | `Patterns` |
| Lema 5.1 | `klDiv_compProd_right_eq_lintegral` | `Entropy` |
| Teorema 5.2 | `ghhsRate_eq`, `ghhsEntropy_eq` | `Entropy` |
| Lema 6.1 | `ghhsEntSup_eq` | `Conjecture` |
| Teorema 6.2 | `ghhsConjecture_12_4` | `Conjecture` |
| Teorema 6.3 | `ghhsConjecture_12_4_bot`, `ghhsConjecture_12_4_bot'` | `Conjecture` |

Las definiciones de [1] están escritas en Lean como sigue.

| Definición de [1] | Definición Lean | Módulo |
|---------------|------------------|------|
| Definición 3.5 (Latinon) | `GHHSLatinon`, `rowMeasure`, `colMeasure`, `IsPermuton` | `Defs` |
| Sección 2.4.1 (norma de corte, reetiquetado) | `graphonCut`, `relabelKernel` | `Distance` |
| Definiciones 4.1, 4.2 | `kernelCut`, `orderGraphon` | `Distance` |
| Definición 4.3 (distancia de corte) | `ghhsCutDistance` | `Distance` |
| Definición 3.7 (densidades) | `ghhsPatternDensity` | `Patterns` |
| Sección 12.2 (entropía) | `ghhsRate`, `ghhsEntropy` | `Entropy` |
| Definición 3.3 (densidades finitas) | `ghhsFiniteDensity` | `Conjecture` |
| Conjetura 12.4 (supremo, conteo) | `ghhsEntSup`, `ghhsCount` | `Conjecture` |

## Agradecimientos

El autor agradece profundamente a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín su amor, paciencia y apoyo.

## Uso de inteligencia artificial y herramientas computacionales

Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, se utilizaron para explorar y comprobar argumentos y para preparar el manuscrito.

Certo [4] se utilizó en el trabajo de [2] en que se apoya esta nota, donde produjo un certificado racional exacto para una constante de la corrección de transporte. Ningún cálculo es premisa de los resultados de esta nota, que descansan en las demostraciones escritas y en el desarrollo en Lean.

El autor es responsable de los argumentos, las citas, el código y la exposición. Ningún sistema de IA figura como autor.

## Referencias

[1] F. Garbe, R. Hancock, J. Hladký y M. Sharifzadeh. *Limits of Latin squares*. Discrete Analysis 2023:8, 66 pp. [doi:10.19086/da.83253](https://doi.org/10.19086/da.83253). [arXiv:2010.07854](https://arxiv.org/abs/2010.07854).

[2] J. P. Traverso Gianini. *Entropy and large deviations for Latin squares*. Preprint 1.0, 16 de noviembre de 2026. <https://github.com/jtraverso/latinon-entropy-ldp>.

[3] The mathlib Community. *The Lean mathematical library*. Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020), 367–381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).

[4] J. P. Traverso Gianini. Certo. Software. <https://github.com/jtraverso/certo-math>.
