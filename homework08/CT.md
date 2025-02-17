```
unify(C) = case C of
  {} -> []
  {t1 = t2} ∪ C' ->
    if t1 == t2 then unify(C)
    else if t1 == α and α not free in t2 then unify([α |-> t2]C') ∘ (α |-> t2)
    else if t2 == α and α not free in t1 then unify([α |-> t1]C') ∘ (α |-> t1)
    else if t1 = t11 -> t12 and t2 = t21 -> t22 then unify({t11 = t21, t12 = t22} ∪ C')         (similarly for other type constructors)
    else FAIL
```

```
      x : t ∈ Γ
----------------------CT-Var
    Γ ⊢ x : t | {} 


        Γ, x : t1 ⊢ e : t2 | C
---------------------------------------------CT-AbsAnnot
    Γ ⊢ (fun x : t1 -> e) : t1 -> t2 | C


        Γ, x : α ⊢ e : t2 | C
---------------------------------------CT-Abs                           α is fresh
    Γ ⊢ (fun x -> e) : α -> t2 | C


             Γ ⊢ e1 : t1 | C1
             Γ ⊢ e2 : t2 | C2        
-------------------------------------------------CT-App                 α is fresh
    Γ ⊢ e1 e2 : α | {t1 = t2 -> α} ∪ C1 ∪ C2



----------------------------CT-True
    Γ ⊢ true : bool | {} 


----------------------------CT-False
    Γ ⊢ false : bool | {} 


        Γ ⊢ e1 : t1 | C2       Γ ⊢ e2 : t2 | C2       Γ ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------CT-ITE
   Γ ⊢ if e1 then e2 else e3 : t2 | { t1 = bool, t2 = t3 } ∪ C1 ∪ C2 ∪ C3

         Γ ⊢ e1 : t1 | C1      Γ ⊢ e2 : t2 | C2
----------------------------------------------------------CT-Pair
             Γ ⊢ (e1, e2) : t1 * t2 | C1 ∪ C2

         Γ ⊢ e : t | C
--------------------------------CT-Fst          α, β are fresh
    Γ ⊢ fst e : α | { t = α * β } ∪ C


         Γ ⊢ e : t | C
--------------------------------CT-Snd          α, β are fresh
    Γ ⊢ snd e : β | { t = α * β } ∪ C


         Γ ⊢ e : t | C
-----------------------------------CT-Inl            α is fresh
      Γ ⊢ inl e : t + α | C 


         Γ ⊢ e : t | C
----------------------------CT-Inr              α is fresh
    Γ ⊢ inr e : α + t | {} 


      Γ ⊢ e1 : t1 | C1       Γ, x : α ⊢ e2 : t2 | C2       Γ, y : β ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------------------CT-Case             α, β are fresh
    Γ ⊢ case e1 of | inl x -> e2  | inr y -> e3 : t2 {t1 = α + β, t2 = t3}  ∪ C1 ∪ C2 ∪ C3


      Γ ⊢ [x ↦ e1]e2 : t2 | C2        Γ ⊢ e1 : t1 | C1
----------------------------------------------------------------CT-LetPoly
            Γ ⊢ let x = e1 in e2 : t2 | C1 ∪ C2
( adapted from 'Types and Programming' by Benjamin C. Pierce : Chapter 22.7 Let-Polymorphism )


      Γ, Γ' ⊢ let f = (fun x -> e1) in f : α | C1           Γ, Γ'' ⊢ e2 : t2 | C2
----------------------------------------------------------------------------------------------CT-LetRec         α is fresh
                Γ ⊢ let rec f x = e1 in e2 : t2 | { t1 = α } ∪ C1 ∪ C2

               where Γ' = f : α, Γ'' = f : Γ^-(t1) Γ^-(τ) = generalize Γ τ    
( adapted from https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Typing_rule )

Γ refers to context (type Ctx in code)
```