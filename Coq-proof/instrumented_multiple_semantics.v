
Add Rec LoadPath "." as DEP_AI.

Require Import language.

Require Import instrumented_values.
Require Import instrumented_semantics.

Require Import instrumented_multiple_values.

Require Import ensembles.

Inductive imval_of : imenv -> expr -> imval -> Prop :=
| IMVal_of :
    forall (imc:imenv) (e:expr) (imv:imval),
      imv = (fun itu =>
               exists (itc:itenv), In _ imc itc
                                   /\ ival_of itc e itu)
      -> imval_of imc e imv.

(*
TODO:
imval_of associe à tout (imc, e) un ensemble de valeur imv

dans le jugement tel que défini ici,
imv représente l'ensemble des valeurs qu'il est possible d'atteindre à partir d'un itc dans imc

Question :
Lorsque e n'a pas de valeur pour certains itc dans imc,
 imv doit-il être vide ?

Réponse :
L'ensemble imc est une abstraction de l'environnement dans lequel va s'évaluer e.
Il représente l'ensemble des environnements possible.
Lorsqu'on donne un jugement imval_of imc e imv,
 on veut obtenir une valeur abstraite imv
 qui nous donne une information sur n'importe quel évaluation possible.

Questions :
Si imv est l'ensemble vide, qu'est-ce que cela signifie ?
- aucune évaluation possible ne fournit de valeur ?
- il existe une évaluation possible qui ne fournit pas de valeur ?

Si imv n'est pas vide, qu'est-ce que cela signifie ?
- il existe une évaluation possible qui termine ?
- toutes les évaluations possibles terminent ?

Réponse :
Dans la sémantique abstraite, la valeur imv est une sur-approximation de la valeur réelle.
Elle doit contenir au moins la valeur réelle.
Donc si il existe une évaluation possible qui termine, sa valeur doit être dans imv.
Même si il existe aussi des évaluations possibles qui ne terminent pas.
*)
