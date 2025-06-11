\documentclass[11pt, a4paper, fleqn]{article}
\usepackage{cp2425t}
\makeindex

%================= lhs2tex=====================================================%
%include polycode.fmt
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const (f)) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (Seq (a)) = "{" a "}^{*}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (lcbr3 (x)(y)(z)) = "\begin{lcbr}" x "\\" y "\\" z "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format Either a b = a "+" b
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textbf{NB}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format outLTree = "\mathsf{out}"
%format inLTree = "\mathsf{in}"
%format inFTree = "\mathsf{in}"
%format outFTree = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format l2 = "l_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format LTree = "{\LTree}"
%format FTree = "{\FTree}"
%format inNat = "\mathsf{in}"
%format (cata (f)) = "\llparenthesis\, " f "\,\rrparenthesis"
%format (cataNat (g)) = "\cataNat{" g "}"
%format (cataList (g)) = "\llparenthesis\, " g "\,\rrparenthesis"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataFTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (cataRose (x)) = "\llparenthesis\, " x "\,\rrparenthesis_\textit{\tiny R}"
%format (ana (g)) = "\ana{" g "}"
%format (anaList (g)) = "\anaList{" g "}"
%format (anaLTree (g)) = "\lanabracket\," g "\,\ranabracket"
%format (anaRose (g)) = "\lanabracket\," g "\,\ranabracket_\textit{\tiny R}"
%format (hylo (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket"
%format (hyloRose (g) (h)) = "\llbracket\, " g ",\," h "\,\rrbracket_\textit{\tiny R}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format delta = "\Delta "
%format (plus (f)(g)) = "{" f "}\plus{" g "}"
%format ++ = "\mathbin{+\!\!+}"
%format Integer  = "\mathbb{Z}"
%format (Cp.cond (p) (f) (g)) = "\mcond{" p "}{" f "}{" g "}"
%format (square (x)) = x "^2"
%format mapAccumL = "\mapAccumL "
%format mapAccumR = "\mapAccumR "

%format (cataTree (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny T}}"
%format (cataForest (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis_{\textit{\tiny F}}"
%format (anaTree (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny T}}"
%format (anaForest (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket_{\textit{\tiny F}}"
%format (hyloTree (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny T}}"
%format (hyloForest (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket_{\textit{\tiny F}}"
%format inTree = "\mathsf{in}_{Tree}"
%format inForest = "\mathsf{in}_{Forest}"
%format outTree = "\mathsf{out}_{Tree}"
%format outForest = "\mathsf{out}_{Forest}"



%format (cata' (f) (g)) = "\llparenthesis\, " f "\:" g "\,\rrparenthesis"
%format (ana' (f) (g)) = "\lanabracket\;\!" f "\:" g "\:\!\ranabracket"
%format (hylo' (ft) (ff) (gt) (gf)) = "\llbracket\, " ft "\:" ff ",\," gt "\:" gf "\,\rrbracket"
%format sigma = "\sigma "
%format alpha = "\alpha "
%format x0 = "x_0 "	
%format h0 = "h_0 "	
%format x1 = "x_1 "	
%format x2 = "x_2 "	
%format x3 = "x_3 "	
%format x4 = "x_4 "	
%format test1 = "test_{1} "	
%format test2a = "test_{2a} "	
%format test2b = "test_{2b} "	
%format test2c = "test_{2c} "	
%format picalc = "\pi_{\mathit{calc}}"	
%format piloop = "\pi_{\mathit{loop}}"	
%format (List.fac (n)) = n " ! "
%format X1 = "X_1 "	
%format X2 = "X_2 "	
%format X3 = "X_3 "	
%format .! = "\mathbin{\bullet}"
%format `ominus` = "\mathbin{\ominus}"
%format (ominus (n)(m)) = "{" n "}\ominus{" m "}"
%format (negb (a))  = "\overline{ " a "}"
%------------------------------------------------------------------------------%

%====== DEFINIR GRUPO E ELEMENTOS =============================================%

\group{G02}
\studentA{108395}{José Pedro Flores Novais }
\studentB{108840}{Guilherme Dall'Agnol }
\studentC{108653}{João Manuel Pinto Alves }

%==============================================================================%

\begin{document}

\sffamily
\setlength{\parindent}{0em}
\emergencystretch 3em
\renewcommand{\baselinestretch}{1.25} 
\input{Cover}
\pagestyle{pagestyle}
\setlength{\parindent}{1em}
\newgeometry{left=25mm,right=20mm,top=25mm,bottom=25mm}

\section*{Preâmbulo}

Na UC de \CP\ pretende-se ensinar a progra\-mação de computadores como uma disciplina
científica. Para isso parte-se de um repertório de \emph{combinadores} que
formam uma álgebra da programação % (conjunto de leis universais e seus corolários)
e usam-se esses combinadores para construir programas \emph{composicionalmente},
isto é, agregando programas já existentes.

Na sequência pedagógica dos planos de estudo dos cursos que têm esta disciplina,
opta-se pela aplicação deste método à programação em \Haskell\ (sem prejuízo
da sua aplicação a outras linguagens funcionais). Assim, o presente trabalho
prático coloca os alunos perante problemas concretos que deverão ser implementados
em \Haskell. Há ainda um outro objectivo: o de ensinar a documentar programas,
a validá-los e a produzir textos técnico-científicos de qualidade.

Antes de abordarem os problemas propostos no trabalho, os grupos devem ler
com atenção o anexo \ref{sec:documentacao} onde encontrarão as instruções
relativas ao \emph{software} a instalar, etc.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções simples
e elegantes que utilizem os combinadores de ordem superior estudados na disciplina.

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where
import Cp
import List hiding (odds)
import Nat hiding (aux)
import LTree hiding (alpha)
import FTree
import Exp
-- import Probability
import Data.List hiding (find,transpose)
-- import Svg hiding (for,dup,fdiv)
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
import Data.Char
import Data.Matrix
import Control.Concurrent
import Cp (assocr, mult)
import Data.Tuple (uncurry)
import Control.Arrow (ArrowChoice(left, right))



main = undefined
\end{code}
%endif

\Problema
Esta questão aborda um problema que é conhecido pela designação '\emph{Container
With Most Water}' e que se formula facilmente através do exemplo da figura
seguinte:

	\histogramaA \label{fig:histogramaA}

\noindent
A figura mostra a sequência de números
\begin{code}
hghts = [1,8,6,2,5,4,8,3,7]
\end{code}
representada sob a forma de um histograma. O que se pretende é obter a maior
área rectangular delimitada por duas barras do histograma, área essa marcada
a azul na figura. (A ``metáfora'' \emph{container with most water} sugere que
as barras selecionadas delimitam um \emph{container} com água.)

Pretende-se definida como um catamorfismo, anamorfismo ou hilomorfismo uma
função em \Haskell
\begin{code}
mostwater :: [Int] -> Int
\end{code}
que deverá dar essa área. (No exemplo acima tem-se |mostwater [1,8,6,2,5,4,8,3,7] = 49|.)
A resolução desta questão deverá ser acompanhada de diagramas elucidativos.

\Problema

Um dos problemas prementes da Computação na actualidade é conseguir, por
engenharia reversa, interpretar as redes neuronais (\NN{RN}) geradas artificialmente
sob a forma de algoritmos compreensíveis por humanos.

Já foram dados passos que, nesse sentido, explicam vários padrões de \NN{RN}s
em termos de combinadores funcionais \cite{Co15}. Em particular, já se mostrou
como as {\RNN}s (\emph{Recurrent Neural Networks}) podem ser vistas como
instâncias de \emph{accumulating maps}, que em \Haskell\ correspondem às
funções |mapAccumR| e |mapAccumL|, conforme o sentido em que a acumulação
se verifica (cf.\ figura \ref{fig:RNNAsMapAccumR}).

\RNNAsMapAccumR

A \RNN\ que a figura \ref{fig:RNNAsMapAccumR} mostra diz-se \emph{'one-to-one'}
\cite{Ka15}. Há contudo padrões de {\RNN}s mais gerais: por exemplo, o padrão
\emph{'many-to-one'} que se mostra na figura \ref{fig:RNNs} extraída
de  \cite{Ka15}.

Se |mapAccumR| e |mapAccumL| juntam |maps| com |folds|, pretendemos agora
combinadores que a isso acrescentem |filter|, por forma a selecionar que
etapas da computação geram ou não \emph{outputs} --- obtendo-se assim o efeito
\emph{'many-to-one'}. Ter-se-á, para esse efeito:

\begin{code}
mapAccumRfilter :: ((a,s) -> Bool) -> ((a, s) -> (c, s)) -> ([a], s) -> ([c], s)
mapAccumLfilter :: ((a,s) -> Bool) -> ((a, s) -> (c, s)) -> ([a], s) -> ([c], s)
\end{code}

Pretende-se a implementação de |mapAccumRfilter| e |mapAccumLfilter| sob a forma de ana / cata ou hilomorfismos em \Haskell, acompanhadas por diagramas.

Como caso de uso, sugere-se o que se dá no anexo \ref{sec:karpathy} que, inspirado em \cite{Ka15}, recorre à biblioteca \DataMatrix.

\Problema

Umas das fórmulas conhecidas para calcular o número |pi| é a que se segue,
\begin{eqnarray}
	|pi| = \sum_{n=0}^\infty \frac{(n!)^2 {2^{n+1}}}{(2n+1)!}
	\label{eq:pi}
\end{eqnarray}
correspondente à função |picalc| cuja implementação em Haskell, paramétrica em |n|, é dada no anexo \ref{sec:codigo}.

Pretende-se uma implementação eficiente de (\ref{eq:pi}) que, derivada por recursividade mútua,
não calcule factoriais nenhuns:
\begin{spec}
piloop = cdots . for loop inic where cdots
\end{spec}
\textbf{Sugestão}: recomenda-se a \textbf{regra prática} que se dá no anexo \ref{sec:mr}
para problemas deste género, que podem envolver várias decomposições por recursividade
mútua em |Nat0|.

\RNNs

\Problema
Considere-se a matriz e o vector que se seguem:
\begin{eqnarray}
mat&=&\begin{bmatrix}
      1 & -1 & 2 \\
      0 & -3 & 1
      \end{bmatrix}
      \label{eq:mat}
\\
vec&=&\begin{bmatrix}
      2  \\
      1 \\
      0
      \end{bmatrix}
      \label{eq:vec}
\end{eqnarray}
Em \Haskell, podemos tornar explícito o espaço vectorial a que (\ref{eq:vec}) pertence definindo-o da forma seguinte,
\begin{code}
vec :: Vec X
vec = V [(X1,2),(X2,1),(X3,0)]
\end{code}
assumindo definido o tipo
\begin{code}
data Vec a = V {outV :: [(a,Int)] } deriving (Ord)
\end{code}
e o ``tipo-dimensão'':
\begin{code}
data X = X1 | X2 | X3 deriving (Eq,Show,Ord)
\end{code}

Da mesma forma que \emph{tipamos} |vec|, também o podemos fazer para a matrix |mat| (\ref{eq:mat}), cujas colunas podem ser indexadas por |X| também e as linhas por |Bool|, por exemplo:
\begin{code}
mat :: X -> Vec Bool
mat X1 = V [(False,1),(True,0)]
mat X2 = V [(False,-1),(True,-3)]
mat X3 = V [(False,2),(True,1)]
\end{code}
Quer dizer, matrizes podem ser encaradas como funções que dão vectores como
resultado. Mais ainda, a multiplicação de |mat| por |vec| pode ser obtida
correndo, simplesmente
\begin{code}
vec' = vec >>= mat
\end{code}
obtendo-se |vec' = V [(False,1),(True,-3)]| do tipo |Vec Bool|.
Finalmente, se for dada a matrix
\begin{code}
neg :: Bool -> Vec Bool
neg False = V [(False,0),(True,1)]
neg True  = V [(False,1),(True,0)]
\end{code}
então a multiplicação de |neg| por |mat| mais não será que a matriz
\begin{spec}
neg .! mat
\end{spec}
também do tipo |X -> Vec Bool|.

Obtém-se assim uma \emph{álgebra linear tipada}. Contudo, para isso é preciso
mostrar que |Vec| é um \textbf{mónade}, e é esse o tema desta questão, em duas partes:
\begin{itemize}
\item	
Instanciar |Vec| na class |Functor| em \Haskell:
\begin{spec}
instance Functor Vec where
    fmap f = ....
\end{spec}
\item	
Instanciar |Vec| na class |Monad| em \Haskell:
\begin{spec}
instance Monad Vec where
   x >>= f = ....
   return a = ...
\end{spec}
\end{itemize} 

\part*{Anexos}

\appendix

\section{Natureza do trabalho a realizar}
\label{sec:documentacao}
Este trabalho teórico-prático deve ser realizado por grupos de 3 alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo em \textbf{todos}
os exercícios do trabalho, para assim poderem responder a qualquer questão
colocada na \emph{defesa oral} do relatório.

Para cumprir de forma integrada os objectivos do trabalho vamos recorrer
a uma técnica de programa\-ção dita ``\litp{literária}'' \cite{Kn92}, cujo
princípio base é o seguinte:
%
\begin{quote}\em
	Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o \textbf{código fonte} e a \textbf{documentação} de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2425t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2425t.lhs}\footnote{O sufixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no \MaterialPedagogico\
desta disciplina des\-com\-pactando o ficheiro \texttt{cp2425t.zip}.

Como se mostra no esquema abaixo, de um único ficheiro (|lhs|)
gera-se um PDF ou faz-se a interpretação do código \Haskell\ que ele inclui:

	\esquema

Vê-se assim que, para além do \GHCi, serão necessários os executáveis \PdfLatex\ e
\LhsToTeX. Para facilitar a instalação e evitar problemas de versões e
conflitos com sistemas operativos, é recomendado o uso do \Docker\ tal como
a seguir se descreve.

\section{Docker} \label{sec:docker}

Recomenda-se o uso do \container\ cuja imagem é gerada pelo \Docker\ a partir do ficheiro
\texttt{Dockerfile} que se encontra na diretoria que resulta de descompactar
\texttt{cp2425t.zip}. Este \container\ deverá ser usado na execução
do \GHCi\ e dos comandos relativos ao \Latex. (Ver também a \texttt{Makefile}
que é disponibilizada.)

Após \href{https://docs.docker.com/engine/install/}{instalar o Docker} e
descarregar o referido zip com o código fonte do trabalho,
basta executar os seguintes comandos:
\begin{Verbatim}[fontsize=\small]
    $ docker build -t cp2425t .
    $ docker run -v ${PWD}:/cp2425t -it cp2425t
\end{Verbatim}
\textbf{NB}: O objetivo é que o container\ seja usado \emph{apenas} 
para executar o \GHCi\ e os comandos relativos ao \Latex.
Deste modo, é criado um \textit{volume} (cf.\ a opção \texttt{-v \$\{PWD\}:/cp2425t}) 
que permite que a diretoria em que se encontra na sua máquina local 
e a diretoria \texttt{/cp2425t} no \container\ sejam partilhadas.

Pretende-se então que visualize/edite os ficheiros na sua máquina local e que
os compile no \container, executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2425t.lhs > cp2425t.tex
    $ pdflatex cp2425t
\end{Verbatim}
\LhsToTeX\ é o pre-processador que faz ``pretty printing'' de código \Haskell\
em \Latex\ e que faz parte já do \container. Alternativamente, basta executar
\begin{Verbatim}[fontsize=\small]
    $ make
\end{Verbatim}
para obter o mesmo efeito que acima.

Por outro lado, o mesmo ficheiro \texttt{cp2425t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2425t.lhs
\end{Verbatim}

\noindent Abra o ficheiro \texttt{cp2425t.lhs} no seu editor de texto preferido
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Em que consiste o TP}

Em que consiste, então, o \emph{relatório} a que se referiu acima?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2425t.aux
    $ makeindex cp2425t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. (Como já se disse, pode fazê-lo
correndo simplesmente \texttt{make} no \container.)

No anexo \ref{sec:codigo} disponibiliza-se algum código \Haskell\ relativo
aos problemas que são colocados. Esse anexo deverá ser consultado e analisado
à medida que isso for necessário.

Deve ser feito uso da \litp{programação literária} para documentar bem o código que se
desenvolver, em particular fazendo diagramas explicativos do que foi feito e
tal como se explica no anexo \ref{sec:diagramas} que se segue.

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2TeX} \label{sec:diagramas}

Como primeiro exemplo, estudar o texto fonte (\lhstotex{lhs}) do que está a ler\footnote{
Procure e.g.\ por \texttt{"sec:diagramas"}.} onde se obtém o efeito seguinte:\footnote{Exemplos
tirados de \cite{Ol05}.}
\begin{eqnarray*}
\start
|
	id = split f g
|
\just\equiv{ universal property }
|
     lcbr(
          p1 . id = f
     )(
          p2 . id = g
     )
|
\just\equiv{ identity }
|
     lcbr(
          p1 = f
     )(
          p2 = g
     )
|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo à \emph{package} \Xymatrix, por exemplo:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Regra prática para a recursividade mútua em |Nat0|}\label{sec:mr}

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol05}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) pode derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como
exemplo o cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci,
recordar o sistema:
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol05} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos de apoio às aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}
Teste relativo à figura da página \pageref{fig:histogramaA}:
\begin{code}
test1 = mostwater hghts
\end{code}

\subsection*{Problema 2}\label{sec:karpathy}

\RNNcharseq

Testes relativos a |mapAccumLfilter| e |mapAccumRfilter| em geral (comparar os \emph{outputs})

\begin{code}
test2a = mapAccumLfilter ((>10).p1) f (odds 12,0)
test2b = mapAccumRfilter ((>10).p1) f (odds 12,0)
\end{code}
onde:
\begin{code}
odds n = map ((1+).(2*)) [0..n-1]
f(a,s) = (s,a+s)
\end{code}
Teste 
\begin{code}
test2c = mapAccumLfilter true step ([x1,x2,x3,x4],h0)
\end{code}
baseado no exemplo de Karpathy \cite{Ka15} que a figura \ref{fig:RNNcharseq} mostra, usando os dados seguintes:
\begin{itemize}
\item	Estado inicial:
\begin{code}
h0 = fromList 3 1 [1.0,1.0,1,0]
\end{code}
\item \emph{Step function}:
\begin{code}
step(x,h) = (alpha(wy * h), alpha(wh * h + wx * x))
\end{code}
\item Função de activação:
\begin{code}
alpha= fmap sigma where sigma x = (tanh x + 1) / 2
\end{code}
\item \emph{Input layer}:
\begin{code}
inp = [x1,x2,x3,x4]
x1 = fromList 4 1 [1.0,0,0,0]
x2 = fromList 4 1 [0,1.0,0,0]
x3 = fromList 4 1 [0,0,1.0,0]
x4 = x3
\end{code}
\item Matrizes exemplo:
\begin{code}
wh = fromList 3 3 [0.4,-0.2,1.6,-3.1,1.4,0.1,5.4,-2.7,0.1]
wy = fromList 4 3 [2.1,1.1,0.8,1.3,-6.4,-3.4,-2.7,-3.8,-1.3,-0.5,-0.9,-0.4]
wx = fromLists  [[0.0,-51.9,0.0,0.0],[0.0,26.6,0.0,0.0],[-16.7,-5.5,-0.1,0.1]]
\end{code}
\end{itemize}
\textbf{NB}: Podem ser definidos e usados outros dados em função das experiências que se queiram fazer.

\subsection*{Problema 3}
Fórmula (\ref{eq:pi}) em Haskell:
\begin{code}
picalc n = (sum . map f) [0..n] where
     f n = fromIntegral ((List.fac n) * (List.fac n)*(g n)) / fromIntegral (d n)
     g n = 2^(n+1)
     d n = List.fac ((2*n+1))
\end{code}

\subsection*{Problema 4}
Se pedirmos ao \GHCi\ que nos mostre o vector |vec| obteremos:
\begin{verbatim}
{ X1 |-> 2 , X2 |-> 1 }
\end{verbatim}
Este resultado aparece mediante a seguinte instância de |Vec| na classe |Show|:
\begin{code}
instance (Show a, Ord a, Eq a) => Show (Vec a) where
    show = showbag . consol . outV  where
       showbag = concat .
                 (++ [" }"]) .  ("{ ":) . 
                 (intersperse " , ") .
                 sort . 
                 (map f) where f(a,b) = (show a) ++ " |-> " ++ (show b)
\end{code}
Outros detalhes da implementação de |Vec| em Haskell:
\begin{code}
instance Applicative Vec where
    pure = return
    (<*>) = aap

instance (Eq a) => Eq (Vec a) where
   b == b' = (outV b) `lequal` (outV b')
           where lequal a b = isempty (a `ominus` b)
                 ominus a b = a ++ negb b
                 negb x = [(k,-i) | (k,i) <- x]
\end{code}
Funções auxiliares:
\begin{code}
consol :: (Eq b) => [(b, Int)] -> [(b, Int)]
consol = filter nzero . map (id >< sum) . col where nzero(_,x)=x/=0

isempty :: Eq a => [(a, Int)] -> Bool
isempty = all (==0) . map snd . consol

col :: (Eq a, Eq b) => [(a, b)] -> [(a, [b])]
col x = nub [ k |-> [ d' | (k',d') <- x , k'==k ] | (k,d) <- x ] where a |-> b = (a,b)
\end{code}




%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o ``layout'' que se fornece.
Não podem ser alterados os nomes ou tipos das funções dadas, mas pode ser
adicionado texto ao anexo, bem como diagramas e/ou outras funções auxiliares
que sejam necessárias.

\noindent
\textbf{Importante}: Não pode ser alterado o texto deste ficheiro fora deste anexo.

\subsection*{Problema 1}
O Problema 1 foi resolvido utilizando um \textit{hilomorfismo}, 
que consiste em um \textit{anamorfismo} que "faz pouco" e um 
\textit{catamorfismo} que "faz muito" — ou seja, uma abordagem do 
tipo \textit{Easy Split / Hard Join}.

Começamos com o \textit{anamorfismo}:


\begin{code}
mysuffixes :: [a] -> [[a]]
mysuffixes = anaList ((id -|- split cons p2) . outList)
\end{code}

De seguida, podemos começar pela cabeça de cada 
sublista e realizar uma busca exaustiva na lista de listas.


\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |Nat0|^*
    \ar[r]^-{|mysuffixes|}
&
    (|Nat0|^*)^*
    \ar[r]_-{|map(split head tail)|}
&
    |Nat0 >< Nat0|^*
}
\end{eqnarray*}

No final, após realizar a procura e o cálculo em todas as sublistas, 
aplicamos o \textit{catamorfismo} \textit{mymaximum}, que extrai o maior
 elemento de uma lista.

\begin{code}
mymaximum :: [Int] -> Int
mymaximum = cataList (either (const 0) (uncurry max))
\end{code}
Como de cada sublista calculada obtemos a área máxima, 
ficamos com uma lista de áreas máximas. Assim, aplicamos o cálculo do máximo sobre essa lista.
\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |Nat0|^*
    \ar[r]^-{|mymaximum|}
&
    |Nat0|   
}
\end{eqnarray*} 
\textbf{Neste passo}, necessitamos de uma função \textit{area}
 que, a partir de um par \textit{head} e \textit{tail}, efectue o cálculo tendo 
 sempre em conta a cabeça.

\begin{code}
area :: (Int,[Int]) -> Int
\end{code}
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0 >< Nat0|^*
    \ar[d]_-{|id >< ((map swap) . zip [1..])|}
    \ar[rr]^{|area|}
&
&
    |Nat0|
\\
    |Nat0 >< (Nat0 >< Nat0)|^*
    \ar[d]_-{|split (id >< len) p2|}
&
& 
\\
    |(Nat0 >< Nat0) >< (Nat0 >< Nat0)|^*
    \ar[d]_-{|(uncurry replicate . swap)>< id|}
&
&  
\\
    |Nat0|^* |>< (Nat0 >< Nat0)|^*
    \ar[r]_-{|uncurry zip|}
&
    (|Nat0 >< (Nat0 >< Nat0)|)^*
    \ar[r]_-{|map auxarea|} 
&   
    |Nat0|^*
    \ar[uuu]_-{|mymaximum|} 
}
\end{eqnarray*}
Temos como função auxiliar a \textit{auxarea}, que efectua o cálculo e 
determina qual dos extremos é o menor para calcular a área.
\begin{code}
auxarea :: (Int,(Int,Int)) -> Int
\end{code}

Recordo que, no par |Nat0 >< (Nat0 >< Nat0)|, a \textbf{primeira componente} é a 
\textit{head}, ou seja, uma das alturas que estamos a calcular; a \textbf{segunda componente} 
é a segunda altura; e, por fim, a \textbf{última componente} é a respetiva distância entre as 
duas alturas. Basta agora verificar qual das alturas é a menor e multiplicar pela distância.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0 >< (Nat0 >< Nat0)|
    \ar[r]^-{|assocl|}
    \ar[d]_-{|auxarea|}
&
    |(Nat0 >< Nat0) >< Nat0|  
    \ar[r]^-{|(grd uncurry (>)) >< id|}
&
    |((Nat0 >< Nat0) + (Nat0 >< Nat0)) >< Nat0|
    \ar[ld]^-{|(either p2 p1) >< id|}
\\
    |Nat0|
&
    |Nat0 >< Nat0|
    \ar[l]^-{|uncurry (*)|}
&  
}
\end{eqnarray*}
Podemos agora exprimir as funções \textit{area} e \textit{auxarea} em \Haskell\ da seguinte forma:
\begin{code}

auxarea = uncurry (*) . (either p2 p1 >< id) . (grd (uncurry (>)) >< id) . assocl

area = mymaximum . map auxarea . uncurry zip . (uncurry replicate . swap >< id ) . split (id >< length) p2  . (id >< map swap . zip [1..])
\end{code}
Finalmente, temos uma definição para o \textit{mostwater}, que pode ser representada no seguinte diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |Nat0|^*
    \ar[d]_-{|mysuffixes|}
    \ar[rrdd]^-{|mostwater|}
\\
& 
    (|Nat0|^*)^*
    \ar[d]_-{|map(split head tail)|}
\\
&
    (|Nat0 >< Nat0|^*)^*
    \ar[r]_-{|map area|}
&
    |Nat0|^*
    \ar[r]_-{|mymaximum|}
&
    |Nat0|
}
\end{eqnarray*}
Para transformar num hilomorfismo de listas, podemos utilizar algumas leis 
do \cp{Cálculo de Programas}, nomeadamente a 
\textit{Composição de maps} e a \textit{Absorção-Cata}.

\begin{eqnarray*}
\start
|
	mostwater = mymaximum . map area . map (split head tail)  . mysuffixes
|
\just\equiv{Functor-F}
|
    mostwater = mymaximum . map (area . (split head tail)) . mysuffixes
|
\just\equiv{mymaximum-definition}
|
    mostwater = cataList(either (const 0) (uncurry max)) . map (area . (split head tail)) . mysuffixes
|
\just\equiv{Absorção-cata}
|
    mostwater = cataList(either (const 0) (uncurry max) . (1 + ((area . split head tail) >< id))) . mysuffixes
|
\just\equiv{Absorção-+, mysuffixes-definition}
|
    mostwater = cataList(either (const 0) (uncurry max . ((area . split head tail) >< id))) . anaList((id + split cons p2) . outList)
|
\qed
\end{eqnarray*}
Temos a definição de \textit{mostwater} como um \textit{hilomorfismo}:
\begin{code}
mostwater = hyloList (either (const 0) (uncurry max . ((area . split head tail) >< id)))  ((id -|- split cons p2) . outList)
\end{code}
Podemos agora exprimir o \textit{mostwater} no seu diagrama de \textit{hilomorfismo}, 
evidenciando o seu \textit{divide} e o seu \textit{conquer}, bem como explicitando a sua 
estrutura intermédia:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|^*
    \ar[r]^-{|out|_*}
    \ar[d]_-{|divide|}
&
    |1 + Nat0 >< Nat0|^*
    \ar[r]^-{|(id + split cons p2)|}
&
    |1 + Nat0|^* |>< Nat0|^*
    \ar[d]^-{|id + id >< divide|}
\\
    (|Nat0|^*)^*
    \ar[d]_-{conquer}
    \ar@@/^/[rr]^-{|out|_{**}}
&
&
    |1 + Nat0|^* |><| ( |Nat0|^*)^*
    \ar@@/^/[ll]^-{in_{**}}
    \ar[d]^{|id + id >< conquer|}
\\
    |Nat0|
&
&
    |1+ Nat0|^* |>< Nat0|
    \ar[ll]^-{|either (const 0) (uncurry max . ((area . split head tail) >< id))|} 
}
\end{eqnarray*}



\subsection*{Problema 2}

Para resolver este problema, foi criada uma estrutura que facilita a visualização da solução.


\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^* |>< S|
    \ar@@/^/[r]^-{|outLP|}
&
   |1 >< S| + |A|^* | >< (A|^* |>< S)|
    \ar@@/^/[l]^-{|inLP|}
}
\end{eqnarray*}
Tal que o \textit{inLP} é definido como a construção
 de uma lista, mantendo o valor da segunda componente:

\begin{code}
inLP = either (nil >< id) ((uncurry (++) >< id) . assocl)
\end{code}
O \textit{outLP} é definido como uma alternativa entre a primeira componente 
ser a lista vazia ou não, colocando assim o único valor numa lista.

\begin{code}
outLP ([],s) = i1 ((),s)
outLP (h:t,s) = i2 (singl h,(t,s))
\end{code}

Com o \textit{inLP} e o \textit{outLP} definidos, 
podemos definir o seu functor recursivo, o que nos 
permite admitir o seu \textit{catamorfismo} e o seu \textit{anamorfismo}.

Começamos pelo \textit{catamorfismo}, 
concretamente o \textit{catamorfismo} identidade, sendo o seu gerador o \textit{inLP}:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^* |>< S|
    \ar[r]^-{|outLP|}
    \ar[d]_-{|cataid|}
&
    |1 >< S| + |A|^* | >< (A|^* |>< S)|
    \ar[d]^-{|id + (id >< cataid)|}
\\
    |A|^* |>< S|
&
    |1 >< S| + |A|^* | >< (A|^* |>< S)|
    \ar[l]^-{|inLP|}
}
\end{eqnarray*}

A correção pode ser confirmada pela análise dos tipos, sabendo-se que esta é análoga ao \textit{anamorfismo}. 
O presente diagrama possibilita a visualização clara do funtor recursivo da estrutura \textbf{LP}, 
definido como:

\begin{code}
recLP f = id -|- (id >< f)
\end{code}
Com o \textit{recLP}, o \textit{inLP} e o \textit{outLP} ja podemos admitir catamorfismo
e anamorfismos
\begin{code}
cataLP g = g . recLP (cataLP g) . outLP

anaLP g = inLP . recLP (anaLP g) . g
\end{code}

Agora, pela ordem natural de \textbf{computação} dos \textit{catamorfismos} e \textit{anamorfismos}, 
podemos definir as funções \textit{mapAccumRfilter} e \textit{mapAccumLfilter} da seguinte forma:

\begin{code}
mapAccumRfilter h f = cataLP (either (nil >< id) (auxR h f))

mapAccumLfilter h f = anaLP ((id -|- auxL h f) . outLP)
\end{code}

Faltam ainda alguns passos de \textbf{cálculo}
para determinar as funções \textit{auxR} e \textit{auxL}. 
Antes disso, apresentam-se os diagramas que explicitam os tipos de ambas as funções.


\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^* |>< S|
    \ar[r]^-{|outLP|}
    \ar[d]_-{|mapAccumRfilter h f|}
&
    |1 >< S| + |A|^* | >< (A|^* |>< S)|
    \ar[d]^-{|id + (id >< mapAccumRfilter h f)|}
\\
    |B|^* |>< S|
&
    |1 >< S| + |A|^* | >< (B|^* |>< S)|
    \ar[l]^-{|either (nil >< id) (auxR h f)|}
}
\end{eqnarray*}

tipo de auxR:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^* | >< (B|^* |>< S)|
    \ar[r]^-{|auxR h f|}
&
    |B|^* |>< S|
}
\end{eqnarray*}
ou em \Haskell:
\begin{code}
auxR :: ((a,s) -> Bool) -> ((a,s) -> (c,s)) -> ([a],([c],s)) -> ([c],s)
\end{code}

Segue-se o desenvolvimento do diagrama a partir do tipo inicial, 
tendo em conta as funções \textit{h} (verificação) e \textit{f} (transformação).

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A|^* | >< (B|^* |>< S)|
    \ar[r]^-{|head >< id|}
&
    |A >< (B|^* |>< S)|
    \ar[d]_-{|split (id >< p2) (assocl . (id >< swap))|}
\\
&
    |(A >< S) >< ((A >< S) >< B|^*)
    \ar[d]_-{|(h >< (f >< id))|}
\\
&
    |2 >< ((B >< S) >< B|^*)
    \ar[d]_-{|grd p1|}
\\
&
    |2 >< ((B >< S) >< B|^*) + |2 >< ((B >< S) >< B|^*)
    \ar[ld]_-{|p2|}
    \ar[rd]^-{|p2|}
    \ar[dd]_-{|choice|}
\\
    |((B >< S) >< B|^*)
    \ar[rd]_-{|swap . ( id >< uncurry (:) ) . assocr . (swap >< id)|}
&
&
    |((B >< S) >< B|^*)
    \ar[ld]^-{|swap . (p2 >< id )|}
\\
&
    |B|^* | >< S|
&
}
\end{eqnarray*}
Apresenta-se a definição de \textit{auxR}:
\begin{code}
auxR h f =  choice . grd p1 . (h >< (f >< id)) . split (id >< p2) (assocl . (id >< swap)) . (head >< id) where
    choice = either (swap . ( id >< uncurry (:) ) . assocr . (swap >< id) . p2) ( swap . (p2 >< id ) . p2)
\end{code}
Segue-se uma definição análoga para \textit{auxL}, partindo de um \textit{anamorfismo}:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |B|^* |>< S|
&
&
    |1 >< S + B|^* |>< (B|^* |>< S)|
    \ar[ll]_-{|inLP|}
\\
|A|^* |>< S|
\ar[u]^-{|mapAccumLfilter|}
\ar[r]_-{|outLP|}
&
    |1 >< S| + |A|^* | >< (A|^* |>< S)|
    \ar[r]_-{|id + auxL h f|}
&
    |1 >< S| + |C|^* | >< (A|^* |>< S)|
    \ar[u]_-{|is + (id >< mapAccumLfilter)|}
}
\end{eqnarray*}

Considera-se, então, o tipo da função \textit{auxL}:

\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |A|^* | >< (A|^* |>< S)|
    \ar[r]_-{|auxL h f|}
&
    |C|^* | >< (A|^* |>< S)|
}
\end{eqnarray*}
Definido em \Haskell\ como:

\begin{code}
auxL :: ((a,s) -> Bool) -> ((a,s) -> (c,s)) -> ([a],([a],s)) -> ([c],([a],s))
\end{code}

Segue-se o desenvolvimento do diagrama a partir do tipo inicial, tendo em conta as 
funções \textit{h} (verificação) e \textit{f} (transformação), com o objetivo de 
alcançar uma conclusão para o código da função \textit{auxL}

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |A >< (S ><| |A|^* |)|
        \ar[d]^-{|assocl|}
    &
    |A|^* |>< (| |A|^* |>< S)|
        \ar[l]^-{|(head >< swap)|}
        \ar[rdddd]^-{|auxL h f|}
\\ 
    |(A >< S) ><| |A|^*
        \ar[d]^-{|(split h f >< id)|}
\\
    |2 >< (C >< S) ><| |A|^*
        \ar[d]^-{|assocr|}
\\ 
    |2 >< ((C >< S) ><| |A|^* |)|
        \ar[d]^-{|(id >< (( id >< swap ) . assocr))|}
\\
    |2 >< (C >< (| |A|^* |>< S))|
        \ar[rr]^-{|choice|}
        \ar[d]^-{|grd p1|}
&
&
    |C|^* |>< (| |A|^* |>< S)|
\\
    |2 >< ((C >< S) ><| |A|^* |) + 2 >< ((C >< S) ><| |A|^* |)|
        \ar[d]^-{|p2 + p2|}
\\
    |(C >< S) ><| |A|^*
        \ar[d]^-{|assocr + assocr|}
\\ 
    |C >< (S ><| |A|^* |) + C >< (S ><| |A|^* |)|
        \ar[d]^-{|( singl >< swap) + (nil >< swap)|}
\\ 
    |C|^* |>< (| |A|^* |>< S) +| |C|^* |>< (| |A|^* |>< S)|
        \ar[r]^-{|either id id|}
&
    |C|^* |>< (| |A|^* |>< S)|
     \ar[ruuuu]^-{|id|}
}
\end{eqnarray*}
Desta forma, obtém-se finalmente a definição de \textit{auxL} em \Haskell:
\begin{code}
auxL h f =  choice  . (id >< (( id >< swap ) . assocr)) . assocr . (split h f >< id) . assocl . (head >< swap) where
    choice = either ((singl >< id) . p2 ) (( nil >< id) . p2) . grd p1
\end{code}

\subsection*{Problema 3}
O Problema 3 foi resolvido por recursividade mútua, tendo como objetivo 
definir as funções que realizam chamadas recursivas mútuas entre si. Para tal, 
é necessária a forma recursiva do somatório em \Haskell.

\begin{code}
picalcRec :: Fractional a => Integer -> a
picalcRec 0 = 2
picalcRec n = fromIntegral (Nat.fac n)^2 * 2^(n+1) / fromIntegral (Nat.fac (2*n+1)) + picalc (n-1)
\end{code}

Como nesta definição existem várias dependências de \(n\), surge a 
necessidade de aplicar a \textit{regra da algibeira}. Assim, para cada 
ocorrência de \(n\), devemos associar uma função qualquer \(f(n-1)\).

\begin{eqnarray*}
\start
|
    n!^2 * 2^{n+1} / (2*n + 1)! + picalc(n-1)
|
\just\equiv{|let f (n-1) = n!|}
|
    f(n-1) = n!
|
    \Rightarrow
|
    f n = (n+1)!
|
    \Rightarrow
|
    lcbr(
        f 0 = 1
    )(
        f n = (n + 1)*f (n-1)
    )
|
\just\equiv{|let f2(n-1) = n+1|}
|
    lcbr(
        lcbr(
            f 0 = 1
        )(
            f n = f2(n-1)*f(n-1)
        )
    )(
        lcbr(
            f2 0 = 2
        )(
            f2 n = n+2
        )
    )
|
\end{eqnarray*}

Feito o procedimento para o \(n!\), aplicamos a mesma regra a
 todas as ocorrências de \(n\) e, por fim, extraímos os seus valores iniciais 
 e operações para o \textit{ciclo for}.

\begin{eqnarray*}
\start
|
    f(n-1)^2 * 2^{n+1} / (2*n + 1)! + picalcRec(n-1)
|
\just\equiv{|let t (n-1) = 2^{n+1}|}
|
    t(n-1) = 2^{n+1}
|
    \Rightarrow
|
    t n = 2^{n+2}
|
    \Rightarrow
|
    lcbr(
        t 0 = 4
    )(
        t n = 2*t(n-1)
    )
|
\end{eqnarray*}

\begin{eqnarray*}
\start
|
    f(n-1)^2 * t(n-1) / (2*n + 1)! + picalc(n-1)
|
\just\equiv{|let g (n-1) = (2*n+1)!|}
|
    g(n-1) = (2*n+1)!
|
    \Rightarrow
|
    g n = (2*n+3)!
|
    \Rightarrow
|
    lcbr(
        g 0 = 6
    )(
        g n = (2*n+2)*(2*n+3)*g (n-1)
    )
|
\just\equiv{|let g1(n-1) = 2*n+2 and g2(n-1) = (2*n+3)|}
|
    lcbr(
        lcbr(
            g1 0 = 4
        )(
            g1 n = 2*n+4
        )
    )(
        lcbr(
            g2 0 = 5
        )(
            g2 n = 2*n+5
        )
    )
|
|
    lcbr(
        g 0 = 6
    )(
        g n = g1(n-1)*g2(n-1)*g(n-1)
    )
|
\end{eqnarray*}
Encontramos finalmente todas as operações e valores iniciais,
obtendo assim a nossa equação do \textit{picalc} neste modelo.

\begin{eqnarray*}
\start
|
    lcbr(
        picalc 0 = 2
    )(
        f(n-1)^2 * t(n-1) / g(n-1) + picalc(n-1)
    )
|
\end{eqnarray*}

Procede-se agora à construção de \textit{piloop} com as 
informações previamente calculadas (para simplificação, designaremos \(s = \textit{picalcRec}\)).

Seguem-se as operações relativas a \(s\):

\textbf{Operação de \(s\):}
\begin{code}
inicS = 2
op_S s f g t =  fromIntegral (f^2*t)/ fromIntegral g + s
\end{code}

\textbf{Operação de \(g\):}
\begin{code}
inicG = 6
op_G g g1 g2 =  g*g1*g2
\end{code}

\textbf{Operação de \(t\):}
\begin{code}
inicT = 4
op_T t = 2*t
\end{code}

\textbf{Operação de \(f\):}
\begin{code}
inicF = 1
op_F f f2 =  f*f2
\end{code}

\textbf{Operação de \(f2\):}
\begin{code}
inicF2 = 2
op_F2 f f2 = succ f2
\end{code}

\textbf{Operação de \(g1\):}
\begin{code}
inicG1 = 4
op_G1 g1 =  g1+2
\end{code}

\textbf{Operação de \(g2\):}
\begin{code}
inicG2 = 5
op_G2 g2 =  g2+2
\end{code}
Dispomos agora de todos os elementos necessários para construir o \textit{ciclo for}.

\begin{code}
worker = for loop inic
\end{code}
Os nossos valores iniciais vão ser os casos bases de cada função que definimos
\begin{code}
inic = (inicS,inicG,inicT,inicF,inicF2,inicG1,inicG2)
\end{code}

E as operações ja definimos também:
\begin{code}
loop (s,g,t,f,f2,g1,g2) = 
                          (op_S s f g t,
                           op_G g g1 g2,
                           op_T t,
                           op_F f f2,
                           op_F2 f f2,
                           op_G1 g1,
                           op_G2 g2
                           )
\end{code}
Por fim, é necessário filtrar apenas o resultado, que corresponde à 
primeira componente do tuplo:
\begin{code}
wrapper (x,_,_,_,_,_,_) = x
\end{code}

Finalmente, obtém-se a função construída com base num \textit{ciclo for}.

\begin{code}
piloop = wrapper . worker
\end{code}

\subsection*{Problema 4}

Começa-se por resolver o functor aplicado a \textit{Vec}, o qual terá os seguintes tipos:
\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |Vec A|
    \ar[r]^-{|fmap f|}
&
    |Vec B|
}
\end{eqnarray*}

Assim, chegamos facilmente à definição explícita deste functor, apresentada no seguinte diagrama:

\[
\centerline{
    \xymatrix@@C=3cm{
        |Vec A|
        \ar[d]^-{|outV|}
    \\
        |(A >< Int)|^*
        \ar[d]^-{|map(f >< id)|}
    \\
        |(B >< Int)|^*
        \ar[d]^-{|V|}
    \\
        |Vec B|
    }
}
\]

Em \Haskell, a definição é dada por:

\begin{code}
instance Functor Vec where
    fmap f = V . map (f >< id) . outV
\end{code}

Deve agora definir-se o operador \((>>=)\) e a função \textit{return} desta \textit{Monad}. 
Para tal, será necessário dispor de \(\mu\) para facilitar os cálculos e 
garantir a completude do problema.

O nosso \(\mu\) terá, naturalmente, os seguintes tipos:

\begin{eqnarray*}
\xymatrix@@C=2cm{
&
    |Vec (Vec A)|
    \ar[r]^-{\mu}
&
    |Vec A|
}
\end{eqnarray*}
Iniciaremos, então, a resolução do diagrama, nomeando a nossa função \(\mu\) como:
\textit{miuV}:
\[
\centerline{
\xymatrix@@C=3cm@@R=1.5cm{
        |Vec (Vec A)|
            \ar[d]_-{|outV|}
    \\
        |(Vec A >< Int)|^*
            \ar[d]_-{|(outV >< id)|}
            \ar@@/^2pc/[ddr]^-{|concatMap (miuaux . (outV >< id))|}
    \\
        |((A >< Int)|^*| >< Int)|^*
            \ar[d]_-{|map miuaux|}
    \\
        |(A >< Int)|^{*^*}
            \ar[r]_-{|concat|}
    &
        (|A >< Int|)^*
            \ar[d]_-{|V|}
    \\
    &
        |Vec A|
    }
}
\]

Será igualmente necessário definir o \textit{miuaux}, que 
realizará a multiplicação de todos os elementos do vetor associado ao número.

\begin{code}
miuaux :: ([(a,Int)],Int) -> [(a,Int)]
\end{code}

\begin{eqnarray*}
    \xymatrix@@C=3cm{
        |(A >< Int)|^* | >< Int|
            \ar[d]_-{|miuaux|}
            \ar[r]^-{| split id (length) >< id|}
    &
        |((A >< Int)|^* |>< Nat0) >< Int|
            \ar[r]^-{|assocr|}
    &
        |(A >< Int)|^* | >< (Nat0 >< Int)|
            \ar[d]^{|(id >< uncurry replicate)|}
    \\
        |(A >< Int)|^*
    &
        |((A >< Int) >< Int)|^*
        \ar[l]^-{|map((id >< uncurry(*)) . assocr)|}
    &
         |(A >< Int)|^* | >< Int|^*
            \ar[l]^-{|uncurry zip|}
    }
\end{eqnarray*}

Procedeu-se à definição das duas funções em \Haskell.

\begin{code}
miuaux = map ((id >< uncurry (*)) . assocr). uncurry zip . (id >< uncurry replicate) . assocr . (split id length >< id)

miuV :: Vec (Vec a) -> Vec a
miuV = V . concatMap (miuaux . (outV >< id)) . outV
\end{code}

Com o \textit{miuV} definido, é possível calcular facilmente \((x >>= f)\) de
 acordo com a fórmula (88) do formulário de \cp{Cálculo de Programas}.

\begin{eqnarray*}
\start
| x >>= f = (|\mu| . T f)x|
\just\equiv{|substituindo pelo o nosso contexto|}
|
    x >>= f = (miuV . fmap f) x
|
\end{eqnarray*}

Falta ainda calcular a função \textit{return}.
 Sabemos que \(\mu_V \circ \textit{return} = \textit{id}\);
  portanto, a definição de \textit{return} será:

\begin{eqnarray*}
\start
| return = V . singl . split id (const 1)|
\end{eqnarray*}

Associa-se o número 1, dado que este é o elemento
neutro da multiplicação; assim, ao aplicar \(\mu_V\),
todos os elementos são multiplicados por 1, resultando
no mesmo vetor. Expressam-se em \Haskell\ o \textit{binding}
e o \textit{return} da seguinte forma:


\begin{code}
instance Monad Vec where
   x >>= f = miuV (fmap f x)
   return = V . singl . split id (const 1)
\end{code}

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2425t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
