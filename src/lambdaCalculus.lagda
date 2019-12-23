%<*Id>
\begin{code}
id : {A : Set} → A → A
id = λ x → x
\end{code}
%</Id>

%<*Id2>
\begin{code}
id' : {A : Set} → A → A
id' x = x
\end{code}
%</Id2>

%<*trueFalse>
\begin{code}
true : {A : Set} → A → A → A
true x y = x

false : {A : Set} → A → A → A
false x y = y
\end{code}
%</trueFalse>

%<*naturals>
\begin{code}
zero : {A : Set} → (A → A) → A → A
zero suc z = z

one : {A : Set} → (A → A) → A → A
one suc z = suc z

two : {A : Set} → (A → A) → A → A
two suc z = suc (suc z)
\end{code}
%</naturals>

%<*plus>
\begin{code}
plus : {A : Set} → ((A → A) → A → A)
  → ((A → A) → A → A)
  → ((A → A) → A → A)
plus n m = λ suc z → n suc (m suc z)

_+_ : {A : Set} → ((A → A) → A → A)
  → ((A → A) → A → A)
  → ((A → A) → A → A)
_+_ n m suc z = n suc (m suc z)
\end{code}
%</plus>

\begin{code}
data Result {A : Set} : A → Set where
  res : (x : A) → Result x
\end{code}

%<*onePone>
\begin{code}
one+one : {A : Set} → Result (_+_ {A} one one)
one+one = res (λ suc z → suc (suc z))
\end{code}
%</onePone>

%<*list>
\begin{code}
emptyList : {A List : Set} → (A → List → List) → List → List
emptyList _::_ nil = nil

natList : {A List : Set} → (((A → A) → A → A) → List → List) → List → List
natList _::_ nil = one :: (two :: nil)
\end{code}
%</list>

%<*sumList>
\begin{code}
sumList : {A List : Set} → Result (natList {A} {(A → A) → A → A} _+_ zero)
sumList = res (λ suc z → suc (suc (suc z)))
\end{code}
%</sumList>
