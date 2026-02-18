import Std
import DbAppVerification.Framework.SQLDSL.Core

namespace DbAppVerification
namespace Framework

/-- Predicate operators for `Expr`/`Pred` AST composition. -/
infix:55 " === " => Pred.eq
infixr:54 " &&& " => Pred.and
infixr:53 " ||| " => Pred.or

/-- SQL-ish join notation: `join "t2" on "t1.id" == "t2.id"` -/
macro "join " table:str " on " left:str " == " right:str : term =>
  `(JoinSpec.mk $table $left $right)

/--
LINQ-ish query notation:

* `from "t" select ["t.col"]`
* `from "t" where p select ["t.col"]`
* `from "t" using [j1, j2] where p select ["t.col"]`
-/
macro "from " base:str " select " "[" cols:str,* "]" : term =>
  `(({ baseTable := $base, project := [$cols,*] } : Query))

macro "from " base:str " where " pred:term " select " "[" cols:str,* "]" : term =>
  `(({ baseTable := $base, where? := some $pred, project := [$cols,*] } : Query))

macro "from " base:str " using " "[" js:term,* "]" " select " "[" cols:str,* "]" : term =>
  `(({ baseTable := $base, joins := [$js,*], project := [$cols,*] } : Query))

macro "from " base:str " using " "[" js:term,* "]" " where " pred:term " select " "[" cols:str,* "]" : term =>
  `(({ baseTable := $base, joins := [$js,*], where? := some $pred, project := [$cols,*] } : Query))

declare_syntax_cat dsl_stmt
syntax term : dsl_stmt
syntax term " ; " dsl_stmt : dsl_stmt
syntax ident " <-q " term " ; " dsl_stmt : dsl_stmt
syntax "dsl{" dsl_stmt "}" : term

macro_rules
  | `(dsl{ $s:term }) =>
      pure s
  | `(dsl{ $head:term ; $tail:dsl_stmt }) =>
      `(Stmt.seq $head (dsl{ $tail }))
  | `(dsl{ $name:ident <-q $q:term ; $tail:dsl_stmt }) => do
      let n := Lean.Syntax.mkStrLit name.getId.toString
      `(Stmt.letQ $n $q (dsl{ $tail }))

end Framework
end DbAppVerification
