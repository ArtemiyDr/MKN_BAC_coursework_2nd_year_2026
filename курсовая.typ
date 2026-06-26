#import "@preview/great-theorems:0.1.2": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/cetz:0.3.4": *
#import cetz.draw: *


#set page(
  paper: "a4",
  margin: (left: 1cm, right: 1cm, top: 1.5cm, bottom: 3.3cm),
)

#set page(numbering: "1")

#set heading(numbering: "1.")

#set text(12pt)

#show: great-theorems-init

#let theoremCounter = counter("theorem")

#let theorem = mathblock(
    blocktitle: "Теорема",
    counter: theoremCounter,
    bodyfmt: emph,
)

#let corollary = mathblock(
    blocktitle: "Следствие",
    counter: none,
    inset: 10pt,
)

#let lemmaCounter = counter("lemma")

#let lemma = mathblock(
    blocktitle: "Лемма",
    counter: lemmaCounter,
    inset: 10pt,
)

#let proposition = mathblock(
    blocktitle: "Предложение",
    counter: none,
    inset: 10pt,
)

#let definitionCounter = counter("definition")

#let definition = mathblock(
    blocktitle: "Определение",
    counter: definitionCounter, 
    bodyfmt: emph,
)

#let remark = mathblock(
    blocktitle: "Замечание",
    counter: none, 
)

#let example = mathblock(
    blocktitle: "Пример",
    counter: none, 
    inset: 10pt,
)

#let proof = proofblock(prefix: [_Доказательство_:#h(0.5cm)], suffix: [#h(1fr) $square$])

#align(center + top)[
    ФЕДЕРАЛЬНОЕ ГОСУДАРСТВЕННОЕ БЮДЖЕТНОЕ\
    ОБРАЗОВАТЕЛЬНОЕ УЧРЕЖДЕНИЕ ВЫСШЕГО ОБРАЗОВАНИЯ\
    "САНКТ-ПЕТЕРБУРГСКИЙ ГОСУДАРСТВЕННЫЙ УНИВЕРСИТЕТ"\
    (СПбГУ)

    \
    Образовательная программа бакалавриата "Математика"
    #v(1.5em)
    #image("spbu-logo.png", width: 30%)
    #v(1.5em)
    #text(18pt)[Отчет о практике на тему]\
    #text(16pt)[О совпадении функций Буркхольдера в локальном случае.]\
    #v(3em)
    Выполнил студент 2 курса бакалавриата\
    группа 24Б01-мкн\
    Дружинин Артемий Фёдорович\
    #v(3em)
    Научный руководитель:\
     Новиков Михаил Игоревич\
    Инженер-исследователь ММИ им. Л. Эйлера
]
#align(center + bottom)[
    Санкт-Петербург\ 2026
]

#pagebreak()

#outline(title: "Оглавление")

#pagebreak()

= Введение.
    В данной работе представлено изучение вопроса, поставленного в разделе 7.4 [2]: совпадение минимальной бивогнутой и кривовогнутой функций Буркхольдера. В качестве продвижения удалось получить достаточное условие совпадения функций Буркхолдера в достаточно малой полосе.

= Определения и формулировка основных результатов.

\

#definition[
    Пусть $beta in RR$. Будем говорить что функция $f:Omega-->RR, space Omega subset RR^2$, вогнута по направлению $(beta,1)$, если соответствующая функция вогнута:
    $
      t |-> f(x_0 + beta t, y_0 + t), space (x_0,y_0) in Omega
    $
    
    Можно заметить, что если $f$ - гладко в $(x_0,y_0)$, то условие вогнутости можно переформулировать следующим образом:
    $
      (partial^2 f)/(partial(beta,1)^2) (x_0,y_0) dot (beta^2 + 1) = beta^2(partial^2 f )/(partial x^2) (x_0,y_0) + 2beta (partial^2 f )/(partial x partial y) (x_0,y_0) + (partial^2 f )/(partial y^2) (x_0,y_0)<=0
    $
]

#definition[
    Обозначим за $Sigma^epsilon = {(x,y) in RR^2 |  |y|<=epsilon}$ и для функции $f:RR->RR$ определим функции Буркхольдера:
    $
      UU^epsilon (x,y) = inf{G(x,y) | G:Sigma^epsilon --> RR" - вогнутая по "(beta,1), space beta in [-1,1], "а также" space G eq.triple f, "при" space y = plus.minus epsilon}\
      VV^epsilon (x,y) = inf{F(x,y) | F:Sigma^epsilon --> RR" - вогнутая по "(beta,1), space beta in {-1,1}, "а также" space F eq.triple f, "при" space y = plus.minus epsilon}
    $
    Также будем называть эти функции минимальной бивогнутой (или диагонально вогнутой) и кривовогнутой функциями $f$ соответственно.\
    В дальнейших построениях для удобства будем рассматривать $Sigma = Sigma^1, space UU = UU^1, space VV = VV^1$
]
#remark[
    Легко видеть, что $VV<=UU$. Также заметим, что для доказательства $UU eq.not VV$ достаточно показать, что функция $VV$ не вогнута по какому-то из направлений $(beta,1), space beta in (-1,1)$, и наоборот, если $VV$ вогнута по соответствующим направлениям, то она равна $UU$.
]

#theorem[
    Пусть $f:RR->RR$ - гладкая функция, такая что:
    + $f$ имеет конечное число корней
    + $|f(x)| lt.tilde e^((|x|)/delta), space delta>1$
    + $f$ строго выпукло на $RR$ ($f^(prime prime)(x) >0, space x in RR$)
    + Пусть $lambda$ - корень $f^(prime prime prime)$, такой что $f^(prime prime prime) (lambda-epsilon) > f^(prime prime prime) (lambda+epsilon)$ для малого $epsilon>0$. Тогда $f^prime (lambda)>0$.
    Тогда существует такое $epsilon>0$, что $VV^epsilon=UU^epsilon$.
]

#pagebreak()

= Вспомогательные результаты.

#v(1cm)

== Угол.

Пусть функция $m_R$ удовлетворяет дифференциальному уравнению:
$
  m_R^prime (u) + m_R (u) = f(u)
$
Определим функцию $V_R$ на полосе $Sigma_R [v_1,v_2] = {(x,y) in Sigma | v_R (x,y) = x+1-|y| in [v_1,v_2]}$
$
  V_R (x,y) = m_R (v_R)(|y|-1) + f(v_R)
$
\

Аналогично определим $m_L$:
$
  -m_L^prime (u) + m_L (u) = f(u)
$
И $V_L$ на полосе $Sigma_L [v_1,v_2] = {(x,y) in Sigma | v_L (x,y) = x-1+|y| in [v_1,v_2]}$:
$
  V_L (x,y) = m_L (v_L)(1-|y|) + f(v_L)
$

#theorem[ (Теорема 3.1.2 из [2]) Если $m_R^(prime prime) (x)<=0, space x in Sigma_R [v_1,v_2]$ то $V_R$ - диагонально вогнутая функция на всём $Sigma_R [v_1,v_2]$.
]

#theorem[ (Теорема 3.1.3 из [2]) Если $m_L^(prime prime) (x)>=0, space x in Sigma_L [v_1,v_2]$ то $V_L$ - диагонально вогнутая функция на всём $Sigma_L [v_1,v_2]$.
]

#theorem[
    Если $m_R^(prime prime) (x)<=0, space x in Sigma_R [v_1,v_2]$ то:
    $
      V_R - "вогнута по" (beta,1), space beta in [-1,1] <==> m_R^prime (x)>=0, space x in Sigma_R [v_1,v_2]
    $
]
#proof[
    Так как $V_R$ - гладкая при $y<0$, вычислим вторую производную по направлению $(beta,1)$ в этой области (по симметричности проверки вогнутости в такой области будет достаточно):
    $
    (partial^2 V_R)/(partial(beta,1)^2) dot (beta^2 + 1) = beta^2 (m_R^(prime prime) (v_R) (-y-1) + f^(prime prime) (v_R)) - 2beta(-m_R^(prime prime)(v_R)(-y-1)+m_R^prime (v_R)- f^(prime prime)(v_R)) + \ + m_R^(prime prime) (v_R) (-y-1) - 2m_R^prime (v_R) + f^(prime prime) (v_R) = -(beta+1)^2y m_R^(prime prime) (v_R) + (beta^2-1)m_R^prime (v_R) = \ = (beta+1)(-(beta+1)y m_R^(prime prime) (v_R) + (beta-1)m_R^prime (v_R))
    $
    Заметим, что если сократить на $beta+1>=0$, то функция примет линейный вид от $beta$, а значит достаточно проверить ее значения на концах: \
    При $beta = 1$ имеем 
    $
      (partial^2 V_R)/(partial(1,1)^2)<=0 "из условия" m_R^(prime prime)<=0
    $
    При $beta = -1$ имеем 
    $
      (partial^2 V_R)/(partial(-1,1)^2)<=0 <==>-m_R^prime<=0 <==> m_R^prime >=0
    $
]

#theorem[
    Если $m_L^(prime prime) (x)>=0, space x in Sigma_L [v_1,v_2]$ то:
    $
      V_L - "вогнута по" (beta,1), space beta in [-1,1] <==> m_L^prime (x)>=0, space x in Sigma_L [v_1,v_2]
    $
]
#proof[
    Аналогично предыдущему доказательству вычислим вторую производную по направлению $(beta,1)$ в области $y<0$:
    $
    (partial^2 V_L)/(partial(beta,1)^2) dot (beta^2 + 1)= (beta+1)((beta+1)y m_R^(prime prime) (v_R) + (beta-1)m_R^prime (v_R))
    $
    И аналогично же проверим значения на концах: \
    При $beta = 1$ имеем 
    $
      (partial^2 V_L)/(partial(1,1)^2)<=0 "из условия" m_L^(prime prime)>=0
    $
    При $beta = -1$ имеем 
    $
      (partial^2 V_L)/(partial(-1,1)^2)<=0 <==>-m_L^prime<=0 <==> m_L^prime >=0
    $
]

#remark[
    В обоих случаях, так как $m_R^prime, space m_L^prime$ - монотонны, имеет смысл говорить только о значениях $m_R^prime, space m_L^prime$ в крайних точках $v_1,v_2$ или $-oo,+oo$. 
]

#align(center,  canvas({
  scale(2)

  line((-3, 1), (4, 1))
  line((-3, -1), (4, -1))

  line((-3, 0), (4.2, 0), stroke: 0.3pt)
  line((0, -1.4), (0, 1.8), stroke: 0.3pt)

  content((4.45, 0.05), [$x$])
  content((0.15, 1.95), [$y$])

  content((-2.5, 1.2), [$(v_1,1)$])
  content((2.5, 1.2), [$(v_2,1)$])

  content((-2.5, -1.2), [$(v_1,-1)$])
  content((2.5, -1.2), [$(v_2,-1)$])

  line((-2.5, 1), (-1.5, 0), stroke: 1.5pt)
  line((-2.5, -1), (-1.5, 0), stroke: 1.5pt)

  line((-1.5, 1), (-0.5, 0))
  line((-1.5, -1), (-0.5, 0))

  line((-0.5, 1), (0.5, 0))
  line((-0.5, -1), (0.5, 0))

  line((0.5, 1), (1.5, 0))
  line((0.5, -1), (1.5, 0))

  line((1.5, 1), (2.5, 0))
  line((1.5, -1), (2.5, 0))

  line((2.5, 1), (3.5, 0), stroke: 1.5pt)
  line((2.5, -1), (3.5, 0), stroke: 1.5pt)
}))
#align(center)[($m_L$ в полосе $Sigma_L [v_1,v_2]$)]

#v(2cm)

#pagebreak()

== Ромб.

Пусть $omega in RR$, введем следующую функцию на ромбе $Sigma_omega = {(x,y in Sigma | |x+y-omega|<=1)}$ 
$
  V_omega = alpha(x^2 + y^2)+x(f^prime (omega)-2alpha omega) + C
$
Где:
$
  alpha = (m_L (omega)-m_R (omega))/4, space C = alpha(1+omega^2)+f(omega)-omega f^prime (omega)
$

#theorem[ (Теорема 3.3.2 из [2])
    Если существует такое $omega in RR$, что:
    + для $v_R<omega: space m_R^(prime prime)(v_R)<=0, space x in Sigma_R [v_1,omega]$
    + для $v_L>omega: space m_L^(prime prime)(v_L)>=0, space x in Sigma_L [omega,v_2]$
    + выполнено уравнение баланса: $m_R (omega)+m_L (omega) = 2 f^prime (omega)$
    Тогда функция $V$, заданная через $V_R, space V_omega, space V_L$ на $Sigma_R [v_1,omega], space Sigma_omega, space Sigma_L [omega,v_2]$ диагонально вогнута.
]

#remark[
    Уравнение баланса эквивалентно условию $m_R^prime (omega) = m_L^prime (omega)$
]

#theorem[
    Для функции $V$ из предыдущей теоремы, если 
    + $m_R^(prime)(x)>=0, space x in Sigma_R [v_1,omega]$
    + $m_L^(prime)(x)>=0, space x in Sigma_L [omega,v_2]$
    Тогда $V$ вогнуто по $(beta,1), space beta in [-1,1]$
]
#proof[
    Вычислим вторую производную по направлению $(beta,1)$ для функции $V_omega$:
    $
      (partial^2 V_omega)/(partial(beta,1)^2) dot (beta^2 + 1)= 2 beta^2 alpha - 2 alpha= 2alpha(beta-1)(beta+1)
    $
    Можем сократить на $beta+1>=0$ - тогда выражение примет линейный вид от $beta$ и останется проверить только случай $beta = -1$: 
    $
      -4alpha<=0 <==>m_L (omega) - m_R (omega) >=0<==>m_L^(prime) (omega) + m_R^(prime) (omega)>=0 <==> m_L^(prime) (omega)>=0 "- следует из условия."
    $
    Таким образом доказали вогнутость внутри ромба, вогнутость в полосах $Sigma_R [v_1,omega], space Sigma_L [omega,v_2]$ также следует из условия, остается проверить вогнутость на границе ромба, так как там возможен скачок первой производной, по симметричности проверим только для $y<0$. 

    Рассмотрим сначала часть с $x>=omega$ - нужно проверить следующее:
    $
      (partial V_omega)/(partial(beta,1))<=(partial V_L)/(partial(beta,1))<==> 2 alpha(beta(x-omega)-y)+beta f^prime (omega)<= (beta-1)y m_L^prime (omega) + m_L (omega)beta
    $
    Это выражение сразу линейно по $beta$, поэтому проверить необходимо только в крайних точках $beta = plus.minus 1$, а для них неравенство выполняется из диагональной вогнутости $V$. Аналогичная логика работает и для случая $x<=omega$.
]

#align(center,  canvas({
  scale(2)

  line((-3, 1), (4, 1))
  line((-3, -1), (4, -1))

  line((-3, 0), (4.2, 0), stroke: 0.3pt)
  line((0, -1.4), (0, 1.8), stroke: 0.3pt)

  content((4.45, 0.05), [$x$])
  content((0.15, 1.95), [$y$])

  content((-1.5, 1.2), [$(v_1,1)$])
  content((2.5, 1.2), [$(v_2,1)$])

  content((-1.5, -1.2), [$(v_1,-1)$])
  content((2.5, -1.2), [$(v_2,-1)$])

  content((0.5, 1.2), [$(omega,1)$])
  content((0.5, -1.2), [$(omega,-1)$])
  content((0.5, 0.2), [$V_omega$])
  content((-1.2, 0.2), [$V_R$])
  content((2.3, 0.2), [$V_L$])

  line((-1.5, 1), (-2.5, 0), stroke: 1.5pt)
  line((-1.5, -1), (-2.5, 0), stroke: 1.5pt)

  line((0.5, 1), (-0.5, 0))
  line((0.5, -1), (-0.5, 0))

  line((0.5, 1), (1.5, 0))
  line((0.5, -1), (1.5, 0))

  line((2.5, 1), (3.5, 0), stroke: 1.5pt)
  line((2.5, -1), (3.5, 0), stroke: 1.5pt)
}))
#align(center)[(конструкция из теоремы 6 в промежутке $[v_1,v_2]$)]

#v(2cm)

== Ёлочка.

Введём новые гладкие функции $a,b:[0,2]-->RR, space a(1) = lambda =b(1)$ такие что:
$
a^prime (l)<0, space b^prime (l)>0, space l in [0,2]\
b(l)-a(l)=l, space l in [0,2]\
(f(b)-f(a))/(b-a) = (f^prime (b)-f^prime (a))/2, space l in [0,2]\
D_R = f^(prime prime) (b) - (f^prime (b)-f^prime (a))/(b-a) <0, space D_L = f^(prime prime) (a) - (f^prime (b)-f^prime (a))/(b-a) <0, space l in [0,2]\
m_L (a_0) = m_R (b_0) = (f(b_0) - f(a_0))/2, space a_0 = a(0), space b_0 = b(0)
$

Также зададим новую гладкую функцию $A:[0,2]-->RR$:
$
    A^prime (l) dot l - A(l) = -(f(a)D_L+f(b)D_R)/(D_R+D_L)\
    A(2) = (f(a_0)+f(b_0))/2
$ 

Определим $Sigma_(h r b) [a_0,b_0]= Sigma \\ (Sigma_L [-oo,(a_0+b_0)/2] union Sigma_R [(a_0+b_0)/2,oo])$ и функцию $V_(h r b)$ в этой области:
$
  V(x,y) = cases(f(b)+(2(y+1))/l (A(l)-f(b)) "при" x>=(a+b)/2,
                 f(a)+(2(y+1))/l (A(l)-f(a)) "при" x<=(a+b)/2)
$
Причем $l$ однозначно зависит от $a$ и $b$ по инъективности, а сами $a$ и $b$ зависят от $x,y$ следующим образом:
$
  b = x+y-1, space x>=(a+b)/2; space
  a = x-y-1, space x<=(a+b)/2
$

#theorem[(Теорема 4.2.1 из [2]) Если для функции $f$ существуют такие $a,b,a_0,b_0,A$ то функция $V$, определнная как: 
- $V_L$ на $Sigma_L [v_1,(a_0+b_0)/2]$
- $V_R$ на $Sigma_R [(a_0+b_0)/2,v_2]$ 
- $V_(h r b)$ на $Sigma_(h r b)$
$C^1$ гладкая и диагонально вогнута на области определения.
]
#remark[
    Можно заметить, что $a,b$ соответствуют неким параметризациям отрезков $[a_0,lambda], space [lambda,b_0]$ которые вместе задают кривую из $(lambda,-1)$ в $((a_0+b_0)/2,0)$, параметизованную $l in [0,2]$, значения функции $V$ на которой и определяет функция $A$.
]

#theorem[
    Для функции $V$ из предыдущей теоремы: если $f^(prime prime)>0$ на отрезке $[a_0,b_0]$ то $V$ вогнуто по $(beta,1), space beta in [-1,1]$ на области определения.
]
#proof[
    По симметричности будем рассматривать нижнюю половину $y<0$.\
    Пусть $x>=(a+b)/2$, заметим, как ведут себя производные функций $a,b,l$ (формула 4.1.10 из [2]):
    $
      a^prime_x = a^prime_y, space b^prime_x = b^prime_y = 1, space l^prime_x = l^prime_y = 1+D_R/D_L
    $
    Обозначим за $I = (A(l)-f(b))/l$, заметим что $I^prime_x = I^prime_y, space I^(prime prime)_(x x) = I^(prime prime)_(x y) = I^(prime prime)_(y y)$. Теперь посчитаем вторую производную в направлении $(beta,1):$
    $
       (partial^2 V_omega)/(partial(beta,1)^2) dot (beta^2 + 1) = beta^2(f^(prime prime) (b)+2(y+1)I^(prime prime))+2beta(f^(prime prime) (b)+2(y+1)I^(prime prime) + 2I^prime) + f^(prime prime) (b)+2(y+1)I^(prime prime) + 4 I^prime = \ =(beta+1)^2 (f^(prime prime) (b)+2(y+1)I^(prime prime)) + 4(beta+1)I^prime
    $
    Опять же, если сократить на $beta+1>=0$ выражение станет линейным по $beta$ и для $beta=1$ неравенство будет следовать из диагональной вогнутости $V$. Проверим для $beta = -1$:
    $
      I^prime <=0 <==>(l(A^prime (l) dot (1+D_R/D_L) - f^prime (b)) - (1+D_R/D_L)dot (A(l)-f(b)))/(l^2)
    $
    Можем считать $l eq.not 0$ - так как вогнутость в этой точке будет следовать из вогнутости по всем точкам в некоторой её окрестности. Тогда можем упростить, подставив также дифференциальное уравнение на $A$:
    $
      - (1+D_R/D_L) dot (f(a)D_L+f(b)D_R)/(D_R+D_L) - l dot f^prime (b)+(1+D_R/D_L)dot f(b)<=0 <==>f(b)-f(a)-f^prime (b) (b-a)<=0 <==>\ <==>f^prime (b)>= f^prime (a) - " что следует из условия" f^(prime prime)>0
    $ 
    Случай $x<=(a+b)/2$ симметричен в смысле перестановки $a$ и $b$ и изменении знаков первых производных, тогда соответствующее условие кривовогнутости примет вид:
    $
      -f^prime (a)>= -f^prime (b) - " что эквивалентно первому случаю."
    $
]

#align(center,  canvas({
  scale(2)

  line((-3, 1), (4, 1))
  line((-3, -1), (4, -1))

  line((-3, 0), (4.2, 0), stroke: 0.3pt)
  line((0, -1.4), (0, 1.8), stroke: 0.3pt)

  content((4.45, 0.05), [$x$])
  content((0.15, 1.95), [$y$])

  content((-2.5, 1.2), [$(v_1,1)$])
  content((3.5, 1.2), [$(v_2,1)$])

  content((-2.5, -1.2), [$(v_1,-1)$])
  content((3.5, -1.2), [$(v_2,-1)$])

  content((1.5, 1.2), [$(b_0,1)$])
  content((-0.5, 1.2), [$(a_0,1)$])
  content((1.5, -1.2), [$(b_0,-1)$])
  content((-0.5, -1.2), [$(a_0,-1)$])
  content((0.7, -1.2), [$(lambda,-1)$])
  content((0.7, 1.2), [$(lambda,1)$])
  content((-0.7, 0.2), [$V_L$])
  content((1.7, 0.2), [$V_R$])
  content((0.5, 0.6), [$V_(h r b)$])
  content((0.5, -0.6), [$V_(h r b)$])

  line((-2.5, 1), (-1.5, 0), stroke: 1.5pt)
  line((-2.5, -1), (-1.5, 0), stroke: 1.5pt)

  line((-0.5, 1), (0.5, 0))
  line((-0.5, -1), (0.5, 0))

  line((1.5, 1), (0.5, 0))
  line((1.5, -1), (0.5, 0))

  line((3.5, 1), (2.5, 0), stroke: 1.5pt)
  line((3.5, -1), (2.5, 0), stroke: 1.5pt)
}))
#align(center)[(конструкция из теоремы 8 в промежутке $[v_1,v_2]$)]

#v(2cm)

== Склейка основных конструкций.

#definition[(определение 1.5.2 из [2])
    Пусть $G: Sigma -> RR$ — диагонально вогнутая функция. Будем говорить, что функция $G$ экстремальна относительно направления $(1,1)$ в точке $x$, если точка $x$ является концом некоторого отрезка $ell$, второй конец которого лежит на границе множества $Sigma$, отрезок $ell$ параллелен направлению $(1,1)$, ограничение $G|_ell$ является аффинной функцией, а функция $G$ дифференцируема в направлении $(1,1)$ в точке $x$.

    Определение функции, экстремальной относительно направления $(1,-1)$, формулируется полностью аналогично.
]

#theorem[(теорема 1.5.3 из [2])
    Пусть $G: Sigma -> RR$ — полунепрерывная сверху диагонально вогнутая функция, множество точек разрыва которой дискретно. Предположим также, что существует число $epsilon > 1$, такое что $abs(G(x)) <= e^(abs(x_1)/epsilon)$
    для всех $x in Sigma$.
    Предположим, что для любой точки $x$ из внутренности множества $Sigma$ выполняется одно из следующих условий:
    + функция $G$ билинейна в некоторой окрестности точки $x$;
    + функция $G$ аффинна относительно направления $(1,1)$ и экстремальна относительно направления $(1,1)$ в точке $x$;
    + функция $G$ аффинна относительно направления $(1,-1)$ и экстремальна относительно направления $(1,-1)$ в точке $x$;
    + функция $G$ экстремальна одновременно относительно направлений $(1,1)$ и $(1,-1)$ в точке $x$.\
    Тогда $G eq.triple VV$
]
#remark[
    Легко видеть, что склеенные по кускам с $V_L, V_R$ углы, ромбы и ёлочки удовлетворяют этой теореме.
]

#theorem[(Теорема ??? из [1])
    Для гладкой функции $f$, удовлетворяющей условиям 1), 2) теоремы 1, существует такое $epsilon_0>0$, что для полосы $Sigma^epsilon, space epsilon<=epsilon_0$ существует такая комбинация ромбов, углов и ёлочек, пересекающихся только по частям с $V_L, V_R$.
]

#theorem[(Теорема ??? из [1])
    Для гладкой функции $f$, удовлетворяющей условиям 1), 2) теоремы 1, все $lambda_i$, соответствующие ёлочкам в построении $VV$, в точности являются корнями $f^(prime prime prime)$, такие что $f^(prime prime prime) (lambda_i-epsilon) > f^(prime prime prime) (lambda_i+epsilon)$
]
#remark[
    В достаточно малой полосе достаточным условием для кривовогнутости на ёлочке будет $f^(prime prime)>0$ во всех таких $lambda_i$ 
]
#proof[ 
    действительно, это условие значит, что в некоторой окрестности $lambda_i$ вторая производная $f$ также положительна, а значит можно выбрать такое $epsilon$, что $a_0,b_0$ будут пренадлежать этой окрестности. По теореме 9 имеем искомое. 
]

#v(2cm)

= Доказательство основных результатов.

#v(1cm)

#counter("theorem").update(0)

#theorem[
    Пусть $f:RR->RR$ - гладкая функция, такая что:
    + $f$ имеет конечное число корней
    + $|f(x)| lt.tilde e^((|x|)/delta), space delta>1$
    + $f$ строго выпукло на $RR$ ($f^(prime prime)(x) >0, space x in RR$)
    + Пусть $lambda$ - корень $f^(prime prime prime)$, такой что $f^(prime prime prime) (lambda-epsilon) > f^(prime prime prime) (lambda+epsilon)$ для малого $epsilon>0$. Тогда $f^prime (lambda)>0$.
    Тогда существует такое $epsilon>0$, что $VV^epsilon=UU^epsilon$.
]
#proof[
    Проверим кривовогнутость функции $VV^epsilon$, полученной по теореме 11. Сразу можно видеть что во всех ёлочках кривовогнутость на $Sigma_(h r b)$ будет по теореме 9. Остается проверить только значения $m^prime_R = m^prime_L$ в крайних точках. 
    Легко видеть, что в $VV^epsilon$ ёлочки и ромбы чередуются. Пусть ёлочкам с $lambda_i$ соответствуют крайние точки $c_i = (a_0+b_0)/2$, а ромбам $omega_j$. Рассмотрим $m_R^prime (c_i) = m_L^prime (c_i)$:
    $
      m_R^prime (c_i) = f^prime (c_i) - m_R^(prime prime) (c_i) >= f^prime (c_i)
    $
    Так как расстояние между $c_i$ и $lambda_i$ линейно зависит от $epsilon$, можем считать что $epsilon$ достаточно мало, что $f^prime (c_i)>0$.\

    Заметим, что $m_R$ и $m_L$ можно записать следующим образом (как решения соответствующих дифференциальных уравнений):
    $
        m_R (u) = e^(v_1-u)m_R (v_1) + e^(-u) integral_(v_1)^u e^t f^prime (t) d t, space u in [v_1,v_2]\
        m_L (u) = e^(u-v_2)m_R (v_2) + e^u integral_u^v_2 e^(-t) f^prime (t) d t, space u in [v_1,v_2]
    $
    И соответственно через интегрирование по частям:
    $
        m_R^prime (u) = e^(v_1-u)m_R^prime (v_1) + e^(-u) integral_(v_1)^u e^t f^(prime prime) (t) d t\
        m_L^prime (u) = e^(u-v_2)m_R^prime (v_2) + e^(u) integral_u^v_2 e^(-t) f^(prime prime) (t) d t
    $
    Рассматривая $m_L$ на $[omega_(j-1),c_i]$ и $m_R$ на $[c_i, omega_j]$ можно понять, что:
    $
      m_R^prime (omega_(j-1)) = e^(c_i-omega_(j-1))m_R^prime (c_i) + e^(-omega_(j-1)) integral_(c_i)^omega_(j-1) e^t f^(prime prime) (t) d t >0\
      m_L^prime (omega_j) = e^(omega_j-c_i)m_R^prime (c_i) + e^(omega_j) integral_(omega_j)^c_i e^(-t) f^(prime prime) (t) d t>0
    $
    По строгой выпуклости $f$. Таким образом проверили знак $m_R^prime = m_L^prime$ на всех крайних точках,
]
#v(4cm)

= Список литературы.
[1] Paata Ivanisvili, Dmitriy M. Stolyarov, Vasily I. Vasyunin, Pavel B. Zatitskiy, #emph("Bellman Function for Extremal
Problems in BMO II: Evolution"), September 2018\
[2] Dmitriy Stolyarov, Vasily Vasyunin, Pavel Zatitskii, #emph("Martingale transforms of bounded random variables and indicator functions of events"), October 5, 2023

