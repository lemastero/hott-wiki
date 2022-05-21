Package [bussproofs.sty](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/bussproofs/BussGuide2_Smith2012.pdf)

```text
$$\begin{prooftree}
\AxiomC{$\Gamma, \space \Delta \space \vdash A$}
\UnaryInfC{$\Delta, \space \Gamma \space \vdash A$}
\end{prooftree}$$
```

identity

$$\begin{prooftree}
\AxiomC{}
\UnaryInfC{$A \space \vdash A$}
\end{prooftree}$$

exchange

$$\begin{prooftree}
\AxiomC{$\Gamma, \space \Delta \space \vdash A$}
\UnaryInfC{$\Delta, \space \Gamma \space \vdash A$}
\end{prooftree}$$

contraction

$$\begin{prooftree}
\AxiomC{$\Gamma, \space A, \space A \space \vdash B$}
\UnaryInfC{$\Gamma, \space A \space \vdash B$}
\end{prooftree}$$

weakening

$$\begin{prooftree}
\AxiomC{$\Gamma \space \vdash B$}
\UnaryInfC{$\Gamma, \space A \space \vdash B$}
\end{prooftree}$$


Package [AMScd](https://www.jmilne.org/not/Mamscd.pdf)

```text
$$\begin{CD}
F(A) @>{F f }>> F(B)\\
@AAFA @AAFA \\
A @>{f}>> B
\end{CD}$$
```

$$\begin{CD}
F(A) @>{F f }>> F(B)\\
@AAFA @AAFA \\
A @>{f}>> B
\end{CD}$$

Simple use of latex

```text
$\cfrac{a:A \qquad b:B}{ (a,b) \text{ :  } A \vee B}$
```

$\cfrac{a:A \qquad b:B}{ (a,b) \text{ :  } A \vee B}$

```text
$\text{f a} \space \cong \space \forall \text{x. (a -> x) -> f  x}$
$\text{b -> a} \space \cong \space \forall \text{x. (a -> x) -> (b -> x)}$
```

Yoneda

$\text{f a} \space \cong \space \forall \text{x. (a -> x) -> f  x}$

Contravariant Yoneda

$\text{f a} \space \cong \space \forall \text{x. (x -> a) -> f x}$

Yoneda embedding

$\text{b -> a} \space \cong \space \forall \text{x. (a -> x) -> (b -> x)}$
