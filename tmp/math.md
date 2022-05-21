[Inference rules guide](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/bussproofs/BussGuide2_Smith2012.pdf)

identity

$$\begin{prooftree}
\AxiomC{}
\UnaryInfC{$A \space \vdash A$}
\end{prooftree}$$

$$\begin{prooftree}
\AxiomC{$\Gamma, \space \Delta \space \vdash A$}
\UnaryInfC{$\Delta, \space \Gamma \space \vdash A$}
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


Docs for [AMScd](https://www.jmilne.org/not/Mamscd.pdf)

$$\begin{CD}
F(A) @>{F f }>> F(B)\\
@AAFA @AAFA \\
A @>{f}>> B
\end{CD}$$

$\cfrac{a:A \qquad b:B}{ (a,b) \text{ :  } A \vee B}$
