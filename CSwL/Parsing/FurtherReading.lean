import CSwLMeta
import Bib

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Leituras adicionais" =>
%%%
tag := "parsing-further-reading"
file := "FurtherReading"
%%%

:::terse
- Relações em árvores descritas em lógica: {citet Bib.blackburn1993}[]
  (lógica modal), {citet Bib.backofen1995}[] (primeira ordem).
- Análise sintática como dedução: {citet Bib.pereira1983}[]. Teoria
  da análise sintática para linguagens formais: {citet Bib.aho1972}[].
- Combinadores de parsers: {citet Bib.wadler1985}[],
  {citet Bib.hutton1992}[], {citet Bib.jeuring2001}[].
- Algoritmos para qualquer gramática livre de contexto, como CKY e
  Earley: {citet Bib.jurafsky2026}[] (cap. 19), {citet Bib.carroll2022}[],
  {citet Bib.allen1995}[].
- Estruturas de traços e unificação em HPSG: {citet Bib.sag1999}[].
:::

::::full
Lógicas para falar de relações em árvores foram propostas em
{citet Bib.blackburn1993}[] (lógica modal) e em {citet Bib.backofen1995}[]
(lógica de primeira ordem). As relações binárias entre posições que
usamos na seção {ref "parse-trees"}[Árvores Sintáticas] podem ser
facilmente descritas em termos lógicos.

A análise sintática de língua natural pode ser também entendida como um processo
de dedução, muito semelhante à dedução lógica
{citet Bib.pereira1983}[]. A bíblia da análise sintática no contexto da
teoria das linguagens formais é {citet Bib.aho1972}[]. A análise de
fragmentos de língua natural com Prolog é o tema de
{citet Bib.pereira1987}[]. Combinadores de parsers no contexto da
programação funcional são introduzidos em {citet Bib.wadler1985}[] e
recebem discussão adicional em {citet Bib.hutton1992}[]. Exemplos de
combinadores de parsers também podem ser encontrados em
{citet Bib.jeuring2001}[].

:::dev BeforeNextRelease
Enable when CSwFP/9.7 is written, with a `{ref}` to its section, as the
last sentence of the paragraph above: "A abordagem do tratamento de
lacunas com combinadores de parsers na seção … é baseada em
{citet Bib.eijck2003}[]." Then the paragraph: "Formalmente, gramáticas
de extração são mais poderosas que gramáticas livres de contexto, pois
permitem definir linguagens sequencialmente indexadas. Linguagens
sequencialmente indexadas são uma extensão própria das linguagens livres
de contexto, e também das linguagens linearmente indexadas de
{citet Bib.gazdar1988}[]. Remetemos a {citet Bib.eijck2007}[] para mais
detalhes."
:::

Uma linguagem de programação de propósito específico para desenvolver
aplicações multilíngues de língua natural, com a análise sintática no
centro, é o Grammatical Framework, ou GF. O GF é uma linguagem
funcional, especializada na escrita de gramáticas. Ver {citet Bib.ranta2009}[]
e [grammaticalframework.org](https://www.grammaticalframework.org).

Os parsers construídos com combinadores seguem a descida recursiva,
que não aceita regras recursivas à esquerda. Algoritmos que analisam qualquer gramática
livre de contexto, como CKY e Earley, são apresentados no capítulo 19
de {citet Bib.jurafsky2026}[], em {citet Bib.carroll2022}[] e em
{citet Bib.allen1995}[]. {citet Bib.bunt2004}[] reúnem trabalhos sobre
técnicas de análise sintática de língua natural. Estruturas de traços,
unificação e subcategorização são apresentadas no formalismo HPSG em
{citet Bib.sag1999}[]. {citet Bib.bender2024}[]
tratam do uso computacional de gramáticas de grande cobertura no
formalismo HPSG, incluindo a análise sintática com elas.
::::
