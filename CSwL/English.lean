import CSwLMeta
import Bib
import CSwL.Sets

open Verso.Genre Manual
open CSwLMeta

#doc (Manual) "Um fragmento de inglês" =>
%%%
tag := "English"
htmlSplit := .never
file := "English"
%%%

```lean
namespace English
```

# Formas Linguísticas e Traduções para Lógica

:::dev "Alexandre (arademaker)"
aqui entra seção CSwFP/6.1
:::

# Um fragmento do Inglês

:::dev "Alexandre (arademaker)"
aqui entra seção CSwFP/4.2. os exercícios pedem expansoes de uma gramatica inicial, vamos tentar fazer evitando ao máximo redefinições de tipos indutivos.
:::

# FOL como Linguagem de representação

:::dev "Alexandre (arademaker)"
aqui entra seção CSwFP/6.2. Ela usa o fragmento definido na seção anterior que veio da CSwFP/4.2
:::

# Uma Estrutura de Primeira Ordem

:::dev "Alexandre (arademaker)"
aqui entra seção CSwFP/6.3. Deve definir a estrutura para avaliação das fórmulas da seção anterior.

Como já implementamos a semantica de FOL no `FOL.lean`, nesta mesma seção podemos absorver CSwFP/6.4 usando o que já temos em `FOL.lean`
:::




```lean
end English
```
