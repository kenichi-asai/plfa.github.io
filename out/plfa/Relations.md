---
src       : src/plfa/Relations.lagda
title     : "Relations: Inductive definition of relations"
layout    : page
prev      : /Induction/
permalink : /Relations/
next      : /Equality/
---

<pre class="Agda">{% raw %}<a id="170" class="Keyword">module</a> <a id="177" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}" class="Module">plfa.Relations</a> <a id="192" class="Keyword">where</a>{% endraw %}</pre>

After having defined operations such as addition and multiplication,
the next step is to define relations, such as _less than or equal_.

## Imports

<pre class="Agda">{% raw %}<a id="373" class="Keyword">import</a> <a id="380" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Relation.Binary.PropositionalEquality</a> <a id="418" class="Symbol">as</a> <a id="421" class="Module">Eq</a>
<a id="424" class="Keyword">open</a> <a id="429" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html" class="Module">Eq</a> <a id="432" class="Keyword">using</a> <a id="438" class="Symbol">(</a><a id="439" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">_≡_</a><a id="442" class="Symbol">;</a> <a id="444" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a><a id="448" class="Symbol">;</a> <a id="450" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a><a id="454" class="Symbol">)</a>
<a id="456" class="Keyword">open</a> <a id="461" class="Keyword">import</a> <a id="468" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="477" class="Keyword">using</a> <a id="483" class="Symbol">(</a><a id="484" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="485" class="Symbol">;</a> <a id="487" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="491" class="Symbol">;</a> <a id="493" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a><a id="496" class="Symbol">;</a> <a id="498" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">_+_</a><a id="501" class="Symbol">)</a>
<a id="503" class="Keyword">open</a> <a id="508" class="Keyword">import</a> <a id="515" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="535" class="Keyword">using</a> <a id="541" class="Symbol">(</a><a id="542" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a><a id="548" class="Symbol">)</a>{% endraw %}</pre>


## Defining relations

The relation _less than or equal_ has an infinite number of
instances.  Here are a few of them:

    0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
              1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                        2 ≤ 2     2 ≤ 3     ...
                                  3 ≤ 3     ...
                                            ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
<pre class="Agda">{% raw %}<a id="1225" class="Keyword">data</a> <a id="_≤_"></a><a id="1230" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a> <a id="1234" class="Symbol">:</a> <a id="1236" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1238" class="Symbol">→</a> <a id="1240" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="1242" class="Symbol">→</a> <a id="1244" class="PrimitiveType">Set</a> <a id="1248" class="Keyword">where</a>

  <a id="_≤_.z≤n"></a><a id="1257" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="1261" class="Symbol">:</a> <a id="1263" class="Symbol">∀</a> <a id="1265" class="Symbol">{</a><a id="1266" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1271" class="Symbol">}</a>
      <a id="1279" class="Comment">--------</a>
    <a id="1292" class="Symbol">→</a> <a id="1294" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="1299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1301" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1266" class="Bound">n</a>

  <a id="_≤_.s≤s"></a><a id="1306" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="1310" class="Symbol">:</a> <a id="1312" class="Symbol">∀</a> <a id="1314" class="Symbol">{</a><a id="1315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1317" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a> <a id="1319" class="Symbol">:</a> <a id="1321" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="1322" class="Symbol">}</a>
    <a id="1328" class="Symbol">→</a> <a id="1330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1334" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>
      <a id="1342" class="Comment">-------------</a>
    <a id="1360" class="Symbol">→</a> <a id="1362" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1366" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1315" class="Bound">m</a> <a id="1368" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="1370" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="1374" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1317" class="Bound">n</a>{% endraw %}</pre>
Here `z≤n` and `s≤s` (with no spaces) are constructor names, while
`zero ≤ n`, and `m ≤ n` and `suc m ≤ suc n` (with spaces) are types.
This is our first use of an _indexed_ datatype, where the type `m ≤ n`
is indexed by two naturals, `m` and `n`.  In Agda any line beginning
with two or more dashes is a comment, and here we have exploited that
convention to write our Agda code in a form that resembles the
corresponding inference rules, a trick we will use often from now on.

Both definitions above tell us the same two things:

* _Base case_: for all naturals `n`, the proposition `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

* _Base case_: for all naturals `n`, the constructor `z≤n`
  produces evidence that `zero ≤ n` holds.
* _Inductive case_: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

For example, here in inference rule notation is the proof that
`2 ≤ 4`:

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof:
<pre class="Agda">{% raw %}<a id="2652" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#2652" class="Function">_</a> <a id="2654" class="Symbol">:</a> <a id="2656" class="Number">2</a> <a id="2658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="2660" class="Number">4</a>
<a id="2662" class="Symbol">_</a> <a id="2664" class="Symbol">=</a> <a id="2666" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2670" class="Symbol">(</a><a id="2671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="2675" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="2678" class="Symbol">)</a>{% endraw %}</pre>




## Implicit arguments

This is our first use of implicit arguments.  In the definition of
inequality, the two lines defining the constructors use `∀`, very
similar to our use of `∀` in propositions such as:

    +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
_implicit_ and need not be written explicitly; instead, they are
_inferred_ by Agda's typechecker. Thus, we write `+-comm m n` for the
proof that `m + n ≡ n + m`, but `z≤n` for the proof that `zero ≤ n`,
leaving `n` implicit.  Similarly, if `m≤n` is evidence that `m ≤ n`,
we write `s≤s m≤n` for evidence that `suc m ≤ suc n`, leaving both `m`
and `n` implicit.

If we wish, it is possible to provide implicit arguments explicitly by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit:
<pre class="Agda">{% raw %}<a id="3673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3673" class="Function">_</a> <a id="3675" class="Symbol">:</a> <a id="3677" class="Number">2</a> <a id="3679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3681" class="Number">4</a>
<a id="3683" class="Symbol">_</a> <a id="3685" class="Symbol">=</a> <a id="3687" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3691" class="Symbol">{</a><a id="3692" class="Number">1</a><a id="3693" class="Symbol">}</a> <a id="3695" class="Symbol">{</a><a id="3696" class="Number">3</a><a id="3697" class="Symbol">}</a> <a id="3699" class="Symbol">(</a><a id="3700" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3704" class="Symbol">{</a><a id="3705" class="Number">0</a><a id="3706" class="Symbol">}</a> <a id="3708" class="Symbol">{</a><a id="3709" class="Number">2</a><a id="3710" class="Symbol">}</a> <a id="3712" class="Symbol">(</a><a id="3713" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3717" class="Symbol">{</a><a id="3718" class="Number">2</a><a id="3719" class="Symbol">}))</a>{% endraw %}</pre>
One may also identify implicit arguments by name:
<pre class="Agda">{% raw %}<a id="3797" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3797" class="Function">_</a> <a id="3799" class="Symbol">:</a> <a id="3801" class="Number">2</a> <a id="3803" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3805" class="Number">4</a>
<a id="3807" class="Symbol">_</a> <a id="3809" class="Symbol">=</a> <a id="3811" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3815" class="Symbol">{</a><a id="3816" class="Argument">m</a> <a id="3818" class="Symbol">=</a> <a id="3820" class="Number">1</a><a id="3821" class="Symbol">}</a> <a id="3823" class="Symbol">{</a><a id="3824" class="Argument">n</a> <a id="3826" class="Symbol">=</a> <a id="3828" class="Number">3</a><a id="3829" class="Symbol">}</a> <a id="3831" class="Symbol">(</a><a id="3832" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3836" class="Symbol">{</a><a id="3837" class="Argument">m</a> <a id="3839" class="Symbol">=</a> <a id="3841" class="Number">0</a><a id="3842" class="Symbol">}</a> <a id="3844" class="Symbol">{</a><a id="3845" class="Argument">n</a> <a id="3847" class="Symbol">=</a> <a id="3849" class="Number">2</a><a id="3850" class="Symbol">}</a> <a id="3852" class="Symbol">(</a><a id="3853" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="3857" class="Symbol">{</a><a id="3858" class="Argument">n</a> <a id="3860" class="Symbol">=</a> <a id="3862" class="Number">2</a><a id="3863" class="Symbol">}))</a>{% endraw %}</pre>
In the latter format, you may only supply some implicit arguments:
<pre class="Agda">{% raw %}<a id="3958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#3958" class="Function">_</a> <a id="3960" class="Symbol">:</a> <a id="3962" class="Number">2</a> <a id="3964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="3966" class="Number">4</a>
<a id="3968" class="Symbol">_</a> <a id="3970" class="Symbol">=</a> <a id="3972" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3976" class="Symbol">{</a><a id="3977" class="Argument">n</a> <a id="3979" class="Symbol">=</a> <a id="3981" class="Number">3</a><a id="3982" class="Symbol">}</a> <a id="3984" class="Symbol">(</a><a id="3985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="3989" class="Symbol">{</a><a id="3990" class="Argument">n</a> <a id="3992" class="Symbol">=</a> <a id="3994" class="Number">2</a><a id="3995" class="Symbol">}</a> <a id="3997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a><a id="4000" class="Symbol">)</a>{% endraw %}</pre>
It is not permitted to swap implicit arguments, even when named.


## Precedence

We declare the precedence for comparison as follows:
<pre class="Agda">{% raw %}<a id="4161" class="Keyword">infix</a> <a id="4167" class="Number">4</a> <a id="4169" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">_≤_</a>{% endraw %}</pre>
We set the precedence of `_≤_` at level 4, so it binds less tightly
than `_+_` at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.
We write `infix` to indicate that the operator does not associate to
either the left or right, as it makes no sense to parse `1 ≤ 2 ≤ 3` as
either `(1 ≤ 2) ≤ 3` or `1 ≤ (2 ≤ 3)`.


## Decidability

Given two numbers, it is straightforward to compute whether or not the
first is less than or equal to the second.  We don't give the code for
doing so here, but will return to this point in
Chapter [Decidable]({{ site.baseurl }}{% link out/plfa/Decidable.md%}).


## Inversion

In our defintions, we go from smaller things to larger things.
For instance, form `m ≤ n` we can conclude `suc m ≤ suc n`,
where `suc m` is bigger than `m` (that is, the former contains
the latter), and `suc n` is bigger than `n`. But sometimes we
want to go from bigger things to smaller things.

There is only one way to prove that `suc m ≤ suc n`, for any `m`
and `n`.  This lets us invert our previous rule.
<pre class="Agda">{% raw %}<a id="inv-s≤s"></a><a id="5187" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5187" class="Function">inv-s≤s</a> <a id="5195" class="Symbol">:</a> <a id="5197" class="Symbol">∀</a> <a id="5199" class="Symbol">{</a><a id="5200" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5202" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a> <a id="5204" class="Symbol">:</a> <a id="5206" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5207" class="Symbol">}</a>
  <a id="5211" class="Symbol">→</a> <a id="5213" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5217" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5219" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5221" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="5225" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a>
    <a id="5231" class="Comment">-------------</a>
  <a id="5247" class="Symbol">→</a> <a id="5249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5200" class="Bound">m</a> <a id="5251" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5202" class="Bound">n</a>
<a id="5255" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5187" class="Function">inv-s≤s</a> <a id="5263" class="Symbol">(</a><a id="5264" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="5268" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5268" class="Bound">m≤n</a><a id="5271" class="Symbol">)</a> <a id="5273" class="Symbol">=</a> <a id="5275" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5268" class="Bound">m≤n</a>{% endraw %}</pre>
Not every rule is invertible; indeed, the rule for `z≤n` has
no non-implicit hypotheses, so there is nothing to invert.
But often inversions of this kind hold.

Another example of inversion is showing that there is
only one way a number can be less than or equal to zero.
<pre class="Agda">{% raw %}<a id="inv-z≤n"></a><a id="5575" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5575" class="Function">inv-z≤n</a> <a id="5583" class="Symbol">:</a> <a id="5585" class="Symbol">∀</a> <a id="5587" class="Symbol">{</a><a id="5588" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5590" class="Symbol">:</a> <a id="5592" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="5593" class="Symbol">}</a>
  <a id="5597" class="Symbol">→</a> <a id="5599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="5603" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
    <a id="5612" class="Comment">--------</a>
  <a id="5623" class="Symbol">→</a> <a id="5625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5588" class="Bound">m</a> <a id="5627" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="5629" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>
<a id="5634" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#5575" class="Function">inv-z≤n</a> <a id="5642" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a> <a id="5646" class="Symbol">=</a> <a id="5648" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>{% endraw %}</pre>

## Properties of ordering relations

Relations pop up all the time, and mathematicians have agreed
on names for some of the most common properties.

* _Reflexive_. For all `n`, the relation `n ≤ n` holds.
* _Transitive_. For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
* _Anti-symmetric_. For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
* _Total_. For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

* _Preorder_. Any relation that is reflexive and transitive.
* _Partial order_. Any preorder that is also anti-symmetric.
* _Total order_. Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading a
technical paper, this gives you a way to orient yourself, by checking
whether or not it is a preorder, partial order, or total order.  A
careful author will often call out these properties---or their
lack---for instance by saying that a newly introduced relation is a
partial order but not a total order.


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

<pre class="Agda">{% raw %}<a id="7155" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

Give an example of a partial order that is not a total order.

<pre class="Agda">{% raw %}<a id="7266" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.  We follow the
convention in the standard library and make the argument implicit,
as that will make it easier to invoke reflexivity:
<pre class="Agda">{% raw %}<a id="≤-refl"></a><a id="7582" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7589" class="Symbol">:</a> <a id="7591" class="Symbol">∀</a> <a id="7593" class="Symbol">{</a><a id="7594" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a> <a id="7596" class="Symbol">:</a> <a id="7598" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="7599" class="Symbol">}</a>
    <a id="7605" class="Comment">-----</a>
  <a id="7613" class="Symbol">→</a> <a id="7615" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a> <a id="7617" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="7619" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7594" class="Bound">n</a>
<a id="7621" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7628" class="Symbol">{</a><a id="7629" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a><a id="7633" class="Symbol">}</a> <a id="7635" class="Symbol">=</a> <a id="7637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="7641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a> <a id="7648" class="Symbol">{</a><a id="7649" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="7653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7653" class="Bound">n</a><a id="7654" class="Symbol">}</a> <a id="7656" class="Symbol">=</a> <a id="7658" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="7662" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#7582" class="Function">≤-refl</a>{% endraw %}</pre>
The proof is a straightforward induction on the implicit argument `n`.
In the base case, `zero ≤ zero` holds by `z≤n`.  In the inductive
case, the inductive hypothesis `≤-refl {n}` gives us a proof of `n ≤
n`, and applying `s≤s` to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p`
hold, then `m ≤ p` holds.  Again, `m`, `n`, and `p` are implicit:
<pre class="Agda">{% raw %}<a id="≤-trans"></a><a id="8315" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8323" class="Symbol">:</a> <a id="8325" class="Symbol">∀</a> <a id="8327" class="Symbol">{</a><a id="8328" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8330" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a> <a id="8332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a> <a id="8334" class="Symbol">:</a> <a id="8336" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="8337" class="Symbol">}</a>
  <a id="8341" class="Symbol">→</a> <a id="8343" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8345" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8347" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a>
  <a id="8351" class="Symbol">→</a> <a id="8353" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8330" class="Bound">n</a> <a id="8355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8357" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a>
    <a id="8363" class="Comment">-----</a>
  <a id="8371" class="Symbol">→</a> <a id="8373" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8328" class="Bound">m</a> <a id="8375" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="8377" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8332" class="Bound">p</a>
<a id="8379" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8387" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="8397" class="Symbol">_</a>          <a id="8408" class="Symbol">=</a>  <a id="8411" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="8415" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8423" class="Symbol">(</a><a id="8424" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8428" class="Bound">m≤n</a><a id="8431" class="Symbol">)</a> <a id="8433" class="Symbol">(</a><a id="8434" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8438" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8438" class="Bound">n≤p</a><a id="8441" class="Symbol">)</a>  <a id="8444" class="Symbol">=</a>  <a id="8447" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="8451" class="Symbol">(</a><a id="8452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="8460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8428" class="Bound">m≤n</a> <a id="8464" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8438" class="Bound">n≤p</a><a id="8467" class="Symbol">)</a>{% endraw %}</pre>
Here the proof is by induction on the _evidence_ that `m ≤ n`.  In the
base case, the first inequality holds by `z≤n` and must show `zero ≤
p`, which follows immediately by `z≤n`.  In this case, the fact that
`n ≤ p` is irrelevant, and we write `_` as the pattern to indicate
that the corresponding evidence is unused.

In the inductive case, the first inequality holds by `s≤s m≤n`
and the second inequality by `s≤s n≤p`, and so we are given
`suc m ≤ suc n` and `suc n ≤ suc p`, and must show `suc m ≤ suc p`.
The inductive hypothesis `≤-trans m≤n n≤p` establishes
that `m ≤ p`, and our goal follows by applying `s≤s`.

The case `≤-trans (s≤s m≤n) z≤n` cannot arise, since the first
inequality implies the middle value is `suc n` while the second
inequality implies that it is `zero`.  Agda can determine that such a
case cannot arise, and does not require (or permit) it to be listed.

Alternatively, we could make the implicit parameters explicit:
<pre class="Agda">{% raw %}<a id="≤-trans′"></a><a id="9444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9453" class="Symbol">:</a> <a id="9455" class="Symbol">∀</a> <a id="9457" class="Symbol">(</a><a id="9458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9460" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a> <a id="9462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a> <a id="9464" class="Symbol">:</a> <a id="9466" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="9467" class="Symbol">)</a>
  <a id="9471" class="Symbol">→</a> <a id="9473" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9475" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9477" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a>
  <a id="9481" class="Symbol">→</a> <a id="9483" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9460" class="Bound">n</a> <a id="9485" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9487" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a>
    <a id="9493" class="Comment">-----</a>
  <a id="9501" class="Symbol">→</a> <a id="9503" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9458" class="Bound">m</a> <a id="9505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="9507" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9462" class="Bound">p</a>
<a id="9509" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9518" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="9526" class="Symbol">_</a>       <a id="9534" class="Symbol">_</a>       <a id="9542" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="9552" class="Symbol">_</a>          <a id="9563" class="Symbol">=</a>  <a id="9566" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="9570" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9579" class="Symbol">(</a><a id="9580" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9584" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9584" class="Bound">m</a><a id="9585" class="Symbol">)</a> <a id="9587" class="Symbol">(</a><a id="9588" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9592" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9592" class="Bound">n</a><a id="9593" class="Symbol">)</a> <a id="9595" class="Symbol">(</a><a id="9596" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="9600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9600" class="Bound">p</a><a id="9601" class="Symbol">)</a> <a id="9603" class="Symbol">(</a><a id="9604" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9608" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m≤n</a><a id="9611" class="Symbol">)</a> <a id="9613" class="Symbol">(</a><a id="9614" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9618" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9618" class="Bound">n≤p</a><a id="9621" class="Symbol">)</a>  <a id="9624" class="Symbol">=</a>  <a id="9627" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="9631" class="Symbol">(</a><a id="9632" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9444" class="Function">≤-trans′</a> <a id="9641" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9584" class="Bound">m</a> <a id="9643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9592" class="Bound">n</a> <a id="9645" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9600" class="Bound">p</a> <a id="9647" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9608" class="Bound">m≤n</a> <a id="9651" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#9618" class="Bound">n≤p</a><a id="9654" class="Symbol">)</a>{% endraw %}</pre>
One might argue that this is clearer or one might argue that the extra
length obscures the essence of the proof.  We will usually opt for
shorter proofs.

The technique of induction on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on 
values of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `C-c C-c`, `C-c C-,`, and `C-c C-r` commands.


## Anti-symmetry

The third property to prove about comparison is that it is
antisymmetric: for all naturals `m` and `n`, if both `m ≤ n` and `n ≤
m` hold, then `m ≡ n` holds:
<pre class="Agda">{% raw %}<a id="≤-antisym"></a><a id="10416" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10416" class="Function">≤-antisym</a> <a id="10426" class="Symbol">:</a> <a id="10428" class="Symbol">∀</a> <a id="10430" class="Symbol">{</a><a id="10431" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10431" class="Bound">m</a> <a id="10433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10433" class="Bound">n</a> <a id="10435" class="Symbol">:</a> <a id="10437" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="10438" class="Symbol">}</a>
  <a id="10442" class="Symbol">→</a> <a id="10444" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10431" class="Bound">m</a> <a id="10446" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10448" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10433" class="Bound">n</a>
  <a id="10452" class="Symbol">→</a> <a id="10454" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10433" class="Bound">n</a> <a id="10456" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="10458" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10431" class="Bound">m</a>
    <a id="10464" class="Comment">-----</a>
  <a id="10472" class="Symbol">→</a> <a id="10474" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10431" class="Bound">m</a> <a id="10476" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#83" class="Datatype Operator">≡</a> <a id="10478" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10433" class="Bound">n</a>
<a id="10480" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10416" class="Function">≤-antisym</a> <a id="10490" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>       <a id="10500" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>        <a id="10511" class="Symbol">=</a>  <a id="10514" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Equality.html#140" class="InductiveConstructor">refl</a>
<a id="10519" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10416" class="Function">≤-antisym</a> <a id="10529" class="Symbol">(</a><a id="10530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="10534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10534" class="Bound">m≤n</a><a id="10537" class="Symbol">)</a> <a id="10539" class="Symbol">(</a><a id="10540" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="10544" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10544" class="Bound">n≤m</a><a id="10547" class="Symbol">)</a>  <a id="10550" class="Symbol">=</a>  <a id="10553" href="https://agda.github.io/agda-stdlib/v0.17/Relation.Binary.PropositionalEquality.html#1170" class="Function">cong</a> <a id="10558" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="10562" class="Symbol">(</a><a id="10563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10416" class="Function">≤-antisym</a> <a id="10573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10534" class="Bound">m≤n</a> <a id="10577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#10544" class="Bound">n≤m</a><a id="10580" class="Symbol">)</a>{% endraw %}</pre>
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold.

In the base case, both inequalities hold by `z≤n`, and so we are given
`zero ≤ zero` and `zero ≤ zero` and must show `zero ≡ zero`, which
follows by reflexivity.  (Reflexivity of equality, that is, not
reflexivity of inequality.)

In the inductive case, the first inequality holds by `s≤s m≤n` and the
second inequality holds by `s≤s n≤m`, and so we are given `suc m ≤ suc n`
and `suc n ≤ suc m` and must show `suc m ≡ suc n`.  The inductive
hypothesis `≤-antisym m≤n n≤m` establishes that `m ≡ n`, and our goal
follows by congruence.

#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?

<pre class="Agda">{% raw %}<a id="11392" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Total

The fourth property to prove about comparison is that it is total:
for any naturals `m` and `n` either `m ≤ n` or `n ≤ m`, or both if
`m` and `n` are equal.

We specify what it means for inequality to be total:
<pre class="Agda">{% raw %}<a id="11662" class="Keyword">data</a> <a id="Total"></a><a id="11667" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="11673" class="Symbol">(</a><a id="11674" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">m</a> <a id="11676" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11676" class="Bound">n</a> <a id="11678" class="Symbol">:</a> <a id="11680" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="11681" class="Symbol">)</a> <a id="11683" class="Symbol">:</a> <a id="11685" class="PrimitiveType">Set</a> <a id="11689" class="Keyword">where</a>

  <a id="Total.forward"></a><a id="11698" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="11706" class="Symbol">:</a>
      <a id="11714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">m</a> <a id="11716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11676" class="Bound">n</a>
      <a id="11726" class="Comment">---------</a>
    <a id="11740" class="Symbol">→</a> <a id="11742" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="11748" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">m</a> <a id="11750" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11676" class="Bound">n</a>

  <a id="Total.flipped"></a><a id="11755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="11763" class="Symbol">:</a>
      <a id="11771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11676" class="Bound">n</a> <a id="11773" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="11775" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">m</a>
      <a id="11783" class="Comment">---------</a>
    <a id="11797" class="Symbol">→</a> <a id="11799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="11805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11674" class="Bound">m</a> <a id="11807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11676" class="Bound">n</a>{% endraw %}</pre>
Evidence that `Total m n` holds is either of the form
`forward m≤n` or `flipped n≤m`, where `m≤n` and `n≤m` are
evidence of `m ≤ n` and `n ≤ m` respectively.

(For those familiar with logic, the above definition
could also be written as a disjunction. Disjunctions will
be introduced in Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%}).)

This is our first use of a datatype with _parameters_,
in this case `m` and `n`.  It is equivalent to the following
indexed datatype:
<pre class="Agda">{% raw %}<a id="12297" class="Keyword">data</a> <a id="Total′"></a><a id="12302" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12302" class="Datatype">Total′</a> <a id="12309" class="Symbol">:</a> <a id="12311" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="12313" class="Symbol">→</a> <a id="12315" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="12317" class="Symbol">→</a> <a id="12319" class="PrimitiveType">Set</a> <a id="12323" class="Keyword">where</a>

  <a id="Total′.forward′"></a><a id="12332" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12332" class="InductiveConstructor">forward′</a> <a id="12341" class="Symbol">:</a> <a id="12343" class="Symbol">∀</a> <a id="12345" class="Symbol">{</a><a id="12346" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">m</a> <a id="12348" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12348" class="Bound">n</a> <a id="12350" class="Symbol">:</a> <a id="12352" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12353" class="Symbol">}</a>
    <a id="12359" class="Symbol">→</a> <a id="12361" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">m</a> <a id="12363" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="12365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12348" class="Bound">n</a>
      <a id="12373" class="Comment">----------</a>
    <a id="12388" class="Symbol">→</a> <a id="12390" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12302" class="Datatype">Total′</a> <a id="12397" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12346" class="Bound">m</a> <a id="12399" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12348" class="Bound">n</a>

  <a id="Total′.flipped′"></a><a id="12404" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12404" class="InductiveConstructor">flipped′</a> <a id="12413" class="Symbol">:</a> <a id="12415" class="Symbol">∀</a> <a id="12417" class="Symbol">{</a><a id="12418" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">m</a> <a id="12420" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12420" class="Bound">n</a> <a id="12422" class="Symbol">:</a> <a id="12424" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="12425" class="Symbol">}</a>
    <a id="12431" class="Symbol">→</a> <a id="12433" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12420" class="Bound">n</a> <a id="12435" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="12437" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">m</a>
      <a id="12445" class="Comment">----------</a>
    <a id="12460" class="Symbol">→</a> <a id="12462" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12302" class="Datatype">Total′</a> <a id="12469" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12418" class="Bound">m</a> <a id="12471" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#12420" class="Bound">n</a>{% endraw %}</pre>
Each parameter of the type translates as an implicit parameter of each
constructor.  Unlike an indexed datatype, where the indexes can vary
(as in `zero ≤ n` and `suc m ≤ suc n`), in a parameterised datatype
the parameters must always be the same (as in `Total m n`).
Parameterised declarations are shorter, easier to read, and
occasionally aid Agda's termination checker, so we will use them in
preference to indexed types when possible.

With that preliminary out of the way, we specify and prove totality:
<pre class="Agda">{% raw %}<a id="≤-total"></a><a id="13006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13006" class="Function">≤-total</a> <a id="13014" class="Symbol">:</a> <a id="13016" class="Symbol">∀</a> <a id="13018" class="Symbol">(</a><a id="13019" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13019" class="Bound">m</a> <a id="13021" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13021" class="Bound">n</a> <a id="13023" class="Symbol">:</a> <a id="13025" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="13026" class="Symbol">)</a> <a id="13028" class="Symbol">→</a> <a id="13030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="13036" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13019" class="Bound">m</a> <a id="13038" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13021" class="Bound">n</a>
<a id="13040" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13006" class="Function">≤-total</a> <a id="13048" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="13056" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13056" class="Bound">n</a>                         <a id="13082" class="Symbol">=</a>  <a id="13085" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="13093" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="13097" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13006" class="Function">≤-total</a> <a id="13105" class="Symbol">(</a><a id="13106" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13110" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13110" class="Bound">m</a><a id="13111" class="Symbol">)</a> <a id="13113" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="13139" class="Symbol">=</a>  <a id="13142" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="13150" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="13154" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13006" class="Function">≤-total</a> <a id="13162" class="Symbol">(</a><a id="13163" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13167" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13167" class="Bound">m</a><a id="13168" class="Symbol">)</a> <a id="13170" class="Symbol">(</a><a id="13171" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="13175" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13175" class="Bound">n</a><a id="13176" class="Symbol">)</a> <a id="13178" class="Keyword">with</a> <a id="13183" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13006" class="Function">≤-total</a> <a id="13191" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13167" class="Bound">m</a> <a id="13193" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13175" class="Bound">n</a>
<a id="13195" class="Symbol">...</a>                        <a id="13222" class="Symbol">|</a> <a id="13224" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="13232" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13232" class="Bound">m≤n</a>  <a id="13237" class="Symbol">=</a>  <a id="13240" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="13248" class="Symbol">(</a><a id="13249" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="13253" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13232" class="Bound">m≤n</a><a id="13256" class="Symbol">)</a>
<a id="13258" class="Symbol">...</a>                        <a id="13285" class="Symbol">|</a> <a id="13287" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="13295" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13295" class="Bound">n≤m</a>  <a id="13300" class="Symbol">=</a>  <a id="13303" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="13311" class="Symbol">(</a><a id="13312" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="13316" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#13295" class="Bound">n≤m</a><a id="13319" class="Symbol">)</a>{% endraw %}</pre>
In this case the proof is by induction over both the first
and second arguments.  We perform a case analysis:

* _First base case_: If the first argument is `zero` and the
  second argument is `n` then the forward case holds,
  with `z≤n` as evidence that `zero ≤ n`.

* _Second base case_: If the first argument is `suc m` and the
  second argument is `zero` then the flipped case holds, with
  `z≤n` as evidence that `zero ≤ suc m`.

* _Inductive case_: If the first argument is `suc m` and the
  second argument is `suc n`, then the inductive hypothesis
  `≤-total m n` establishes one of the following:

  + The forward case of the inductive hypothesis holds with `m≤n` as
    evidence that `m ≤ n`, from which it follows that the forward case of the
    proposition holds with `s≤s m≤n` as evidence that `suc m ≤ suc n`.

  + The flipped case of the inductive hypothesis holds with `n≤m` as
    evidence that `n ≤ m`, from which it follows that the flipped case of the
    proposition holds with `s≤s n≤m` as evidence that `suc n ≤ suc m`.

This is our first use of the `with` clause in Agda.  The keyword
`with` is followed by an expression and one or more subsequent lines.
Each line begins with an ellipsis (`...`) and a vertical bar (`|`),
followed by a pattern to be matched against the expression
and the right-hand side of the equation.

Every use of `with` is equivalent to defining a helper function.  For
example, the definition above is equivalent to the following:
<pre class="Agda">{% raw %}<a id="≤-total′"></a><a id="14827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14827" class="Function">≤-total′</a> <a id="14836" class="Symbol">:</a> <a id="14838" class="Symbol">∀</a> <a id="14840" class="Symbol">(</a><a id="14841" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14841" class="Bound">m</a> <a id="14843" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14843" class="Bound">n</a> <a id="14845" class="Symbol">:</a> <a id="14847" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="14848" class="Symbol">)</a> <a id="14850" class="Symbol">→</a> <a id="14852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="14858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14841" class="Bound">m</a> <a id="14860" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14843" class="Bound">n</a>
<a id="14862" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14827" class="Function">≤-total′</a> <a id="14871" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="14879" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14879" class="Bound">n</a>        <a id="14888" class="Symbol">=</a>  <a id="14891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="14899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14903" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14827" class="Function">≤-total′</a> <a id="14912" class="Symbol">(</a><a id="14913" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14917" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14917" class="Bound">m</a><a id="14918" class="Symbol">)</a> <a id="14920" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>     <a id="14929" class="Symbol">=</a>  <a id="14932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="14940" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="14944" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14827" class="Function">≤-total′</a> <a id="14953" class="Symbol">(</a><a id="14954" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14958" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14958" class="Bound">m</a><a id="14959" class="Symbol">)</a> <a id="14961" class="Symbol">(</a><a id="14962" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="14966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14966" class="Bound">n</a><a id="14967" class="Symbol">)</a>  <a id="14970" class="Symbol">=</a>  <a id="14973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15005" class="Function">helper</a> <a id="14980" class="Symbol">(</a><a id="14981" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14827" class="Function">≤-total′</a> <a id="14990" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14958" class="Bound">m</a> <a id="14992" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14966" class="Bound">n</a><a id="14993" class="Symbol">)</a>
  <a id="14997" class="Keyword">where</a>
  <a id="15005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15005" class="Function">helper</a> <a id="15012" class="Symbol">:</a> <a id="15014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="15020" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14958" class="Bound">m</a> <a id="15022" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14966" class="Bound">n</a> <a id="15024" class="Symbol">→</a> <a id="15026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="15032" class="Symbol">(</a><a id="15033" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15037" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14958" class="Bound">m</a><a id="15038" class="Symbol">)</a> <a id="15040" class="Symbol">(</a><a id="15041" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15045" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#14966" class="Bound">n</a><a id="15046" class="Symbol">)</a>
  <a id="15050" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15005" class="Function">helper</a> <a id="15057" class="Symbol">(</a><a id="15058" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="15066" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15066" class="Bound">m≤n</a><a id="15069" class="Symbol">)</a>  <a id="15072" class="Symbol">=</a>  <a id="15075" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="15083" class="Symbol">(</a><a id="15084" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15088" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15066" class="Bound">m≤n</a><a id="15091" class="Symbol">)</a>
  <a id="15095" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15005" class="Function">helper</a> <a id="15102" class="Symbol">(</a><a id="15103" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="15111" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15111" class="Bound">n≤m</a><a id="15114" class="Symbol">)</a>  <a id="15117" class="Symbol">=</a>  <a id="15120" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="15128" class="Symbol">(</a><a id="15129" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="15133" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15111" class="Bound">n≤m</a><a id="15136" class="Symbol">)</a>{% endraw %}</pre>
This is also our first use of a `where` clause in Agda.  The keyword `where` is
followed by one or more definitions, which must be indented.  Any variables
bound on the left-hand side of the preceding equation (in this case, `m` and
`n`) are in scope within the nested definition, and any identifiers bound in the
nested definition (in this case, `helper`) are in scope in the right-hand side
of the preceding equation.

If both arguments are equal, then both cases hold and we could return evidence
of either.  In the code above we return the forward case, but there is a
variant that returns the flipped case:
<pre class="Agda">{% raw %}<a id="≤-total″"></a><a id="15774" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15774" class="Function">≤-total″</a> <a id="15783" class="Symbol">:</a> <a id="15785" class="Symbol">∀</a> <a id="15787" class="Symbol">(</a><a id="15788" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15788" class="Bound">m</a> <a id="15790" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15790" class="Bound">n</a> <a id="15792" class="Symbol">:</a> <a id="15794" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="15795" class="Symbol">)</a> <a id="15797" class="Symbol">→</a> <a id="15799" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11667" class="Datatype">Total</a> <a id="15805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15788" class="Bound">m</a> <a id="15807" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15790" class="Bound">n</a>
<a id="15809" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15774" class="Function">≤-total″</a> <a id="15818" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15818" class="Bound">m</a>       <a id="15826" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>                      <a id="15852" class="Symbol">=</a>  <a id="15855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="15863" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="15867" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15774" class="Function">≤-total″</a> <a id="15876" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="15884" class="Symbol">(</a><a id="15885" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15889" class="Bound">n</a><a id="15890" class="Symbol">)</a>                   <a id="15910" class="Symbol">=</a>  <a id="15913" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="15921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1257" class="InductiveConstructor">z≤n</a>
<a id="15925" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15774" class="Function">≤-total″</a> <a id="15934" class="Symbol">(</a><a id="15935" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15939" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15939" class="Bound">m</a><a id="15940" class="Symbol">)</a> <a id="15942" class="Symbol">(</a><a id="15943" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="15947" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15947" class="Bound">n</a><a id="15948" class="Symbol">)</a> <a id="15950" class="Keyword">with</a> <a id="15955" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15774" class="Function">≤-total″</a> <a id="15964" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15939" class="Bound">m</a> <a id="15966" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#15947" class="Bound">n</a>
<a id="15968" class="Symbol">...</a>                        <a id="15995" class="Symbol">|</a> <a id="15997" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="16005" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16005" class="Bound">m≤n</a>   <a id="16011" class="Symbol">=</a>  <a id="16014" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11698" class="InductiveConstructor">forward</a> <a id="16022" class="Symbol">(</a><a id="16023" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16027" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16005" class="Bound">m≤n</a><a id="16030" class="Symbol">)</a>
<a id="16032" class="Symbol">...</a>                        <a id="16059" class="Symbol">|</a> <a id="16061" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="16069" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16069" class="Bound">n≤m</a>   <a id="16075" class="Symbol">=</a>  <a id="16078" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#11755" class="InductiveConstructor">flipped</a> <a id="16086" class="Symbol">(</a><a id="16087" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16091" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16069" class="Bound">n≤m</a><a id="16094" class="Symbol">)</a>{% endraw %}</pre>
It differs from the original code in that it pattern
matches on the second argument before the first argument.


## Monotonicity

If one bumps into both an operator and an ordering at a party, one may ask if
the operator is _monotonic_ with regard to the ordering.  For example, addition
is monotonic with regard to inequality, meaning:

    ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

The proof is straightforward using the techniques we have learned, and is best
broken into three parts. First, we deal with the special case of showing
addition is monotonic on the right:
<pre class="Agda">{% raw %}<a id="+-monoʳ-≤"></a><a id="16699" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="16709" class="Symbol">:</a> <a id="16711" class="Symbol">∀</a> <a id="16713" class="Symbol">(</a><a id="16714" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">n</a> <a id="16716" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">p</a> <a id="16718" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16718" class="Bound">q</a> <a id="16720" class="Symbol">:</a> <a id="16722" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="16723" class="Symbol">)</a>
  <a id="16727" class="Symbol">→</a> <a id="16729" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">p</a> <a id="16731" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16733" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16718" class="Bound">q</a>
    <a id="16739" class="Comment">-------------</a>
  <a id="16755" class="Symbol">→</a> <a id="16757" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">n</a> <a id="16759" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16761" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16716" class="Bound">p</a> <a id="16763" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="16765" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16714" class="Bound">n</a> <a id="16767" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="16769" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16718" class="Bound">q</a>
<a id="16771" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="16781" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>    <a id="16789" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16789" class="Bound">p</a> <a id="16791" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16791" class="Bound">q</a> <a id="16793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16793" class="Bound">p≤q</a>  <a id="16798" class="Symbol">=</a>  <a id="16801" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16793" class="Bound">p≤q</a>
<a id="16805" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="16815" class="Symbol">(</a><a id="16816" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="16820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16820" class="Bound">n</a><a id="16821" class="Symbol">)</a> <a id="16823" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16823" class="Bound">p</a> <a id="16825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16825" class="Bound">q</a> <a id="16827" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16827" class="Bound">p≤q</a>  <a id="16832" class="Symbol">=</a>  <a id="16835" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1306" class="InductiveConstructor">s≤s</a> <a id="16839" class="Symbol">(</a><a id="16840" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="16850" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16820" class="Bound">n</a> <a id="16852" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16823" class="Bound">p</a> <a id="16854" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16825" class="Bound">q</a> <a id="16856" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16827" class="Bound">p≤q</a><a id="16859" class="Symbol">)</a>{% endraw %}</pre>
The proof is by induction on the first argument.

* _Base case_: The first argument is `zero` in which case
  `zero + p ≤ zero + q` simplifies to `p ≤ q`, the evidence
  for which is given by the argument `p≤q`.

* _Inductive case_: The first argument is `suc n`, in which case
  `suc n + p ≤ suc n + q` simplifies to `suc (n + p) ≤ suc (n + q)`.
  The inductive hypothesis `+-monoʳ-≤ n p q p≤q` establishes that
  `n + p ≤ n + q`, and our goal follows by applying `s≤s`.

Second, we deal with the special case of showing addition is
monotonic on the left. This follows from the previous
result and the commutativity of addition:
<pre class="Agda">{% raw %}<a id="+-monoˡ-≤"></a><a id="17515" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Function">+-monoˡ-≤</a> <a id="17525" class="Symbol">:</a> <a id="17527" class="Symbol">∀</a> <a id="17529" class="Symbol">(</a><a id="17530" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">m</a> <a id="17532" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">n</a> <a id="17534" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17534" class="Bound">p</a> <a id="17536" class="Symbol">:</a> <a id="17538" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17539" class="Symbol">)</a>
  <a id="17543" class="Symbol">→</a> <a id="17545" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">m</a> <a id="17547" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17549" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">n</a>
    <a id="17555" class="Comment">-------------</a>
  <a id="17571" class="Symbol">→</a> <a id="17573" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17530" class="Bound">m</a> <a id="17575" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17577" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17534" class="Bound">p</a> <a id="17579" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17581" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17532" class="Bound">n</a> <a id="17583" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17585" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17534" class="Bound">p</a>
<a id="17587" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Function">+-monoˡ-≤</a> <a id="17597" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">m</a> <a id="17599" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">n</a> <a id="17601" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">p</a> <a id="17603" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17603" class="Bound">m≤n</a>  <a id="17608" class="Keyword">rewrite</a> <a id="17616" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="17623" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">m</a> <a id="17625" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">p</a> <a id="17627" class="Symbol">|</a> <a id="17629" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#9708" class="Function">+-comm</a> <a id="17636" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">n</a> <a id="17638" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">p</a>  <a id="17641" class="Symbol">=</a> <a id="17643" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="17653" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17601" class="Bound">p</a> <a id="17655" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17597" class="Bound">m</a> <a id="17657" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17599" class="Bound">n</a> <a id="17659" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17603" class="Bound">m≤n</a>{% endraw %}</pre>
Rewriting by `+-comm m p` and `+-comm n p` converts `m + p ≤ n + p` into
`p + m ≤ p + n`, which is proved by invoking `+-monoʳ-≤ p m n m≤n`.

Third, we combine the two previous results:
<pre class="Agda">{% raw %}<a id="+-mono-≤"></a><a id="17873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17873" class="Function">+-mono-≤</a> <a id="17882" class="Symbol">:</a> <a id="17884" class="Symbol">∀</a> <a id="17886" class="Symbol">(</a><a id="17887" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">m</a> <a id="17889" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">n</a> <a id="17891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">p</a> <a id="17893" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17893" class="Bound">q</a> <a id="17895" class="Symbol">:</a> <a id="17897" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="17898" class="Symbol">)</a>
  <a id="17902" class="Symbol">→</a> <a id="17904" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">m</a> <a id="17906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17908" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">n</a>
  <a id="17912" class="Symbol">→</a> <a id="17914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">p</a> <a id="17916" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17918" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17893" class="Bound">q</a>
    <a id="17924" class="Comment">-------------</a>
  <a id="17940" class="Symbol">→</a> <a id="17942" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17887" class="Bound">m</a> <a id="17944" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17946" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17891" class="Bound">p</a> <a id="17948" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#1230" class="Datatype Operator">≤</a> <a id="17950" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17889" class="Bound">n</a> <a id="17952" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="17954" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17893" class="Bound">q</a>
<a id="17956" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17873" class="Function">+-mono-≤</a> <a id="17965" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17965" class="Bound">m</a> <a id="17967" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">n</a> <a id="17969" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17969" class="Bound">p</a> <a id="17971" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17971" class="Bound">q</a> <a id="17973" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17973" class="Bound">m≤n</a> <a id="17977" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17977" class="Bound">p≤q</a>  <a id="17982" class="Symbol">=</a>  <a id="17985" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#8315" class="Function">≤-trans</a> <a id="17993" class="Symbol">(</a><a id="17994" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17515" class="Function">+-monoˡ-≤</a> <a id="18004" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17965" class="Bound">m</a> <a id="18006" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">n</a> <a id="18008" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17969" class="Bound">p</a> <a id="18010" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17973" class="Bound">m≤n</a><a id="18013" class="Symbol">)</a> <a id="18015" class="Symbol">(</a><a id="18016" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#16699" class="Function">+-monoʳ-≤</a> <a id="18026" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17967" class="Bound">n</a> <a id="18028" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17969" class="Bound">p</a> <a id="18030" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17971" class="Bound">q</a> <a id="18032" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#17977" class="Bound">p≤q</a><a id="18035" class="Symbol">)</a>{% endraw %}</pre>
Invoking `+-monoˡ-≤ m n p m≤n` proves `m + p ≤ n + p` and invoking
`+-monoʳ-≤ n p q p≤q` proves `n + p ≤ n + q`, and combining these with
transitivity proves `m + p ≤ n + q`, as was to be shown.


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.

<pre class="Agda">{% raw %}<a id="18360" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Strict inequality {#strict-inequality}

We can define strict inequality similarly to inequality:
<pre class="Agda">{% raw %}<a id="18509" class="Keyword">infix</a> <a id="18515" class="Number">4</a> <a id="18517" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18527" class="Datatype Operator">_&lt;_</a>

<a id="18522" class="Keyword">data</a> <a id="_&lt;_"></a><a id="18527" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18527" class="Datatype Operator">_&lt;_</a> <a id="18531" class="Symbol">:</a> <a id="18533" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18535" class="Symbol">→</a> <a id="18537" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="18539" class="Symbol">→</a> <a id="18541" class="PrimitiveType">Set</a> <a id="18545" class="Keyword">where</a>

  <a id="_&lt;_.z&lt;s"></a><a id="18554" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18554" class="InductiveConstructor">z&lt;s</a> <a id="18558" class="Symbol">:</a> <a id="18560" class="Symbol">∀</a> <a id="18562" class="Symbol">{</a><a id="18563" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18563" class="Bound">n</a> <a id="18565" class="Symbol">:</a> <a id="18567" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18568" class="Symbol">}</a>
      <a id="18576" class="Comment">------------</a>
    <a id="18593" class="Symbol">→</a> <a id="18595" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a> <a id="18600" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18527" class="Datatype Operator">&lt;</a> <a id="18602" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18606" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18563" class="Bound">n</a>

  <a id="_&lt;_.s&lt;s"></a><a id="18611" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18611" class="InductiveConstructor">s&lt;s</a> <a id="18615" class="Symbol">:</a> <a id="18617" class="Symbol">∀</a> <a id="18619" class="Symbol">{</a><a id="18620" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">m</a> <a id="18622" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18622" class="Bound">n</a> <a id="18624" class="Symbol">:</a> <a id="18626" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="18627" class="Symbol">}</a>
    <a id="18633" class="Symbol">→</a> <a id="18635" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">m</a> <a id="18637" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18527" class="Datatype Operator">&lt;</a> <a id="18639" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18622" class="Bound">n</a>
      <a id="18647" class="Comment">-------------</a>
    <a id="18665" class="Symbol">→</a> <a id="18667" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18671" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18620" class="Bound">m</a> <a id="18673" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18527" class="Datatype Operator">&lt;</a> <a id="18675" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="18679" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#18622" class="Bound">n</a>{% endraw %}</pre>
The key difference is that zero is less than the successor of an
arbitrary number, but is not less than zero.

Clearly, strict inequality is not reflexive. However it is
_irreflexive_ in that `n < n` never holds for any value of `n`.
Like inequality, strict inequality is transitive.
Strict inequality is not total, but satisfies the closely related property of
_trichotomy_: for any `m` and `n`, exactly one of `m < n`, `m ≡ n`, or `m > n`
holds (where we define `m > n` to hold exactly when `n < m`).
It is also monotonic with regards to addition and multiplication.

Most of the above are considered in exercises below.  Irreflexivity
requires negation, as does the fact that the three cases in
trichotomy are mutually exclusive, so those points are deferred to
Chapter [Negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).

It is straightforward to show that `suc m ≤ n` implies `m < n`,
and conversely.  One can then give an alternative derivation of the
properties of strict inequality, such as transitivity, by
exploiting the corresponding properties of inequality.

#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

<pre class="Agda">{% raw %}<a id="19849" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`.

Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation]({{ site.baseurl }}{% link out/plfa/Negation.md%}).)

<pre class="Agda">{% raw %}<a id="20338" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

<pre class="Agda">{% raw %}<a id="20563" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

<pre class="Agda">{% raw %}<a id="20722" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relation between strict inequality and inequality and
the fact that inequality is transitive.

<pre class="Agda">{% raw %}<a id="20998" class="Comment">-- Your code goes here</a>{% endraw %}</pre>


## Even and odd

As a further example, let's specify even and odd numbers.  Inequality
and strict inequality are _binary relations_, while even and odd are
_unary relations_, sometimes called _predicates_:
<pre class="Agda">{% raw %}<a id="21253" class="Keyword">data</a> <a id="even"></a><a id="21258" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="21263" class="Symbol">:</a> <a id="21265" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="21267" class="Symbol">→</a> <a id="21269" class="PrimitiveType">Set</a>
<a id="21273" class="Keyword">data</a> <a id="odd"></a><a id="21278" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a>  <a id="21283" class="Symbol">:</a> <a id="21285" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a> <a id="21287" class="Symbol">→</a> <a id="21289" class="PrimitiveType">Set</a>

<a id="21294" class="Keyword">data</a> <a id="21299" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="21304" class="Keyword">where</a>

  <a id="even.zero"></a><a id="21313" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21313" class="InductiveConstructor">zero</a> <a id="21318" class="Symbol">:</a>
      <a id="21326" class="Comment">---------</a>
      <a id="21342" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="21347" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#115" class="InductiveConstructor">zero</a>

  <a id="even.suc"></a><a id="21355" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21355" class="InductiveConstructor">suc</a>  <a id="21360" class="Symbol">:</a> <a id="21362" class="Symbol">∀</a> <a id="21364" class="Symbol">{</a><a id="21365" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21365" class="Bound">n</a> <a id="21367" class="Symbol">:</a> <a id="21369" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21370" class="Symbol">}</a>
    <a id="21376" class="Symbol">→</a> <a id="21378" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a> <a id="21382" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21365" class="Bound">n</a>
      <a id="21390" class="Comment">------------</a>
    <a id="21407" class="Symbol">→</a> <a id="21409" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="21414" class="Symbol">(</a><a id="21415" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21419" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21365" class="Bound">n</a><a id="21420" class="Symbol">)</a>

<a id="21423" class="Keyword">data</a> <a id="21428" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a> <a id="21432" class="Keyword">where</a>

  <a id="odd.suc"></a><a id="21441" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21441" class="InductiveConstructor">suc</a>   <a id="21447" class="Symbol">:</a> <a id="21449" class="Symbol">∀</a> <a id="21451" class="Symbol">{</a><a id="21452" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21452" class="Bound">n</a> <a id="21454" class="Symbol">:</a> <a id="21456" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="21457" class="Symbol">}</a>
    <a id="21463" class="Symbol">→</a> <a id="21465" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="21470" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21452" class="Bound">n</a>
      <a id="21478" class="Comment">-----------</a>
    <a id="21494" class="Symbol">→</a> <a id="21496" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a> <a id="21500" class="Symbol">(</a><a id="21501" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#128" class="InductiveConstructor">suc</a> <a id="21505" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21452" class="Bound">n</a><a id="21506" class="Symbol">)</a>{% endraw %}</pre>
A number is even if it is zero or the successor of an odd number,
and odd if it is the successor of an even number.

This is our first use of a mutually recursive datatype declaration.
Since each identifier must be defined before it is used, we first
declare the indexed types `even` and `odd` (omitting the `where`
keyword and the declarations of the constructors) and then
declare the constructors (omitting the signatures `ℕ → Set`
which were given earlier).

This is also our first use of _overloaded_ constructors,
that is, using the same name for constructors of different types.
Here `suc` means one of three constructors:

    suc : ℕ → ℕ

    suc : ∀ {n : ℕ}
      → odd n
        ------------
      → even (suc n)

    suc : ∀ {n : ℕ}
      → even n
        -----------
      → odd (suc n)

Similarly, `zero` refers to one of two constructors. Due to how it
does type inference, Agda does not allow overloading of defined names,
but does allow overloading of constructors.  It is recommended that
one restrict overloading to related meanings, as we have done here,
but it is not required.

We show that the sum of two even numbers is even:
<pre class="Agda">{% raw %}<a id="e+e≡e"></a><a id="22682" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22682" class="Function">e+e≡e</a> <a id="22688" class="Symbol">:</a> <a id="22690" class="Symbol">∀</a> <a id="22692" class="Symbol">{</a><a id="22693" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">m</a> <a id="22695" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22695" class="Bound">n</a> <a id="22697" class="Symbol">:</a> <a id="22699" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22700" class="Symbol">}</a>
  <a id="22704" class="Symbol">→</a> <a id="22706" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="22711" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">m</a>
  <a id="22715" class="Symbol">→</a> <a id="22717" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="22722" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22695" class="Bound">n</a>
    <a id="22728" class="Comment">------------</a>
  <a id="22743" class="Symbol">→</a> <a id="22745" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="22750" class="Symbol">(</a><a id="22751" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22693" class="Bound">m</a> <a id="22753" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22755" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22695" class="Bound">n</a><a id="22756" class="Symbol">)</a>

<a id="o+e≡o"></a><a id="22759" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22759" class="Function">o+e≡o</a> <a id="22765" class="Symbol">:</a> <a id="22767" class="Symbol">∀</a> <a id="22769" class="Symbol">{</a><a id="22770" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">m</a> <a id="22772" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22772" class="Bound">n</a> <a id="22774" class="Symbol">:</a> <a id="22776" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#97" class="Datatype">ℕ</a><a id="22777" class="Symbol">}</a>
  <a id="22781" class="Symbol">→</a> <a id="22783" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a> <a id="22787" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">m</a>
  <a id="22791" class="Symbol">→</a> <a id="22793" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21258" class="Datatype">even</a> <a id="22798" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22772" class="Bound">n</a>
    <a id="22804" class="Comment">-----------</a>
  <a id="22818" class="Symbol">→</a> <a id="22820" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21278" class="Datatype">odd</a> <a id="22824" class="Symbol">(</a><a id="22825" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22770" class="Bound">m</a> <a id="22827" href="https://agda.github.io/agda-stdlib/v0.17/Agda.Builtin.Nat.html#230" class="Primitive Operator">+</a> <a id="22829" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22772" class="Bound">n</a><a id="22830" class="Symbol">)</a>

<a id="22833" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22682" class="Function">e+e≡e</a> <a id="22839" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21313" class="InductiveConstructor">zero</a>     <a id="22848" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22848" class="Bound">en</a>  <a id="22852" class="Symbol">=</a>  <a id="22855" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22848" class="Bound">en</a>
<a id="22858" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22682" class="Function">e+e≡e</a> <a id="22864" class="Symbol">(</a><a id="22865" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21355" class="InductiveConstructor">suc</a> <a id="22869" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22869" class="Bound">om</a><a id="22871" class="Symbol">)</a> <a id="22873" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22873" class="Bound">en</a>  <a id="22877" class="Symbol">=</a>  <a id="22880" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21355" class="InductiveConstructor">suc</a> <a id="22884" class="Symbol">(</a><a id="22885" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22759" class="Function">o+e≡o</a> <a id="22891" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22869" class="Bound">om</a> <a id="22894" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22873" class="Bound">en</a><a id="22896" class="Symbol">)</a>

<a id="22899" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22759" class="Function">o+e≡o</a> <a id="22905" class="Symbol">(</a><a id="22906" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21441" class="InductiveConstructor">suc</a> <a id="22910" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22910" class="Bound">em</a><a id="22912" class="Symbol">)</a> <a id="22914" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22914" class="Bound">en</a>  <a id="22918" class="Symbol">=</a>  <a id="22921" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#21441" class="InductiveConstructor">suc</a> <a id="22925" class="Symbol">(</a><a id="22926" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22682" class="Function">e+e≡e</a> <a id="22932" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22910" class="Bound">em</a> <a id="22935" href="{% endraw %}{{ site.baseurl }}{% link out/plfa/Relations.md %}{% raw %}#22914" class="Bound">en</a><a id="22937" class="Symbol">)</a>{% endraw %}</pre>
Corresponding to the mutually recursive types, we use two mutually recursive
functions, one to show that the sum of two even numbers is even, and the other
to show that the sum of an odd and an even number is odd.

This is our first use of mutually recursive functions.  Since each identifier
must be defined before it is used, we first give the signatures for both
functions and then the equations that define them.

To show that the sum of two even numbers is even, consider the
evidence that the first number is even. If it is because it is zero,
then the sum is even because the second number is even.  If it is
because it is the successor of an odd number, then the result is even
because it is the successor of the sum of an odd and an even number,
which is odd.

To show that the sum of an odd and even number is odd, consider the
evidence that the first number is odd. If it is because it is the
successor of an even number, then the result is odd because it is the
successor of the sum of two even numbers, which is even.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.

<pre class="Agda">{% raw %}<a id="24091" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin]({{ site.baseurl }}{% link out/plfa/Naturals.md%}#Bin)
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following:

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

    Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings:

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring:

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity:

    Can x
    ---------------
    to (from x) ≡ x

(Hint: For each of these, you may first need to prove related
properties of `One`.)

<pre class="Agda">{% raw %}<a id="25385" class="Comment">-- Your code goes here</a>{% endraw %}</pre>

## Standard library

Definitions similar to those in this chapter can be found in the standard library:
<pre class="Agda">{% raw %}<a id="25537" class="Keyword">import</a> <a id="25544" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.html" class="Module">Data.Nat</a> <a id="25553" class="Keyword">using</a> <a id="25559" class="Symbol">(</a><a id="25560" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#845" class="Datatype Operator">_≤_</a><a id="25563" class="Symbol">;</a> <a id="25565" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#868" class="InductiveConstructor">z≤n</a><a id="25568" class="Symbol">;</a> <a id="25570" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Base.html#910" class="InductiveConstructor">s≤s</a><a id="25573" class="Symbol">)</a>
<a id="25575" class="Keyword">import</a> <a id="25582" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html" class="Module">Data.Nat.Properties</a> <a id="25602" class="Keyword">using</a> <a id="25608" class="Symbol">(</a><a id="25609" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2115" class="Function">≤-refl</a><a id="25615" class="Symbol">;</a> <a id="25617" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2308" class="Function">≤-trans</a><a id="25624" class="Symbol">;</a> <a id="25626" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2165" class="Function">≤-antisym</a><a id="25635" class="Symbol">;</a> <a id="25637" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#2420" class="Function">≤-total</a><a id="25644" class="Symbol">;</a>
                                  <a id="25680" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12667" class="Function">+-monoʳ-≤</a><a id="25689" class="Symbol">;</a> <a id="25691" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12577" class="Function">+-monoˡ-≤</a><a id="25700" class="Symbol">;</a> <a id="25702" href="https://agda.github.io/agda-stdlib/v0.17/Data.Nat.Properties.html#12421" class="Function">+-mono-≤</a><a id="25710" class="Symbol">)</a>{% endraw %}</pre>
In the standard library, `≤-total` is formalised in terms of
disjunction (which we define in
Chapter [Connectives]({{ site.baseurl }}{% link out/plfa/Connectives.md%})),
and `+-monoʳ-≤`, `+-monoˡ-≤`, `+-mono-≤` are proved differently than here,
and more arguments are implicit.


## Unicode

This chapter uses the following unicode:

    ≤  U+2264  LESS-THAN OR EQUAL TO (\<=, \le)
    ≥  U+2265  GREATER-THAN OR EQUAL TO (\>=, \ge)
    ˡ  U+02E1  MODIFIER LETTER SMALL L (\^l)
    ʳ  U+02B3  MODIFIER LETTER SMALL R (\^r)

The commands `\^l` and `\^r` give access to a variety of superscript
leftward and rightward arrows in addition to superscript letters `l` and `r`.
