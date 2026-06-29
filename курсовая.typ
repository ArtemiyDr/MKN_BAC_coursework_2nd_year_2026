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

#let remarkCounter = counter("remark")

#let remark = mathblock(
    blocktitle: "Замечание",
    counter: remarkCounter, 
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

= Определения и формулировка основного результата.

\

#definition[
    Пусть $beta in RR$. Будем говорить что функция $f:Omega-->RR, space Omega subset RR^2$, вогнута в направлении $(beta,1)$, если соответствующая функция вогнута:
    $
      t |-> f(x_0 + beta t, y_0 + t), space (x_0,y_0) in Omega.
    $
    
    Можно заметить, что если функция $f$ гладкая в точке $(x_0,y_0)$, то условие вогнутости можно переформулировать следующим образом:
    $
      (partial^2 f)/(partial(beta,1)^2) (x_0,y_0) = beta^2(partial^2 f )/(partial x^2) (x_0,y_0) + 2beta (partial^2 f )/(partial x partial y) (x_0,y_0) + (partial^2 f )/(partial y^2) (x_0,y_0)<=0.
    $
]

#definition[
    Введём множество $Sigma^epsilon = {(x,y) in RR^2 |  |y|<=epsilon}$ и для функции $f:RR->RR$ определим функции Буркхольдера:
    $
      UU^epsilon (x,y) = inf{G(x,y) | G:Sigma^epsilon --> RR - "вогнутая вдоль "(beta,1), space beta in [-1,1], "а также" space G eq.triple f, "при" space y = plus.minus epsilon}\
      VV^epsilon (x,y) = inf{F(x,y) | F:Sigma^epsilon --> RR - "вогнутая вдоль "(beta,1), space beta in {-1,1}, "а также" space F eq.triple f, "при" space y = plus.minus epsilon}
    $
    Также будем называть эти функции минимальной диагонально вогнутой и $D$-вогнутой функциями $f$ соответственно.\
    В дальнейших построениях для удобства будем рассматривать $Sigma = Sigma^1, space UU = UU^1, space VV = VV^1$.
]
#remark[
    Легко видеть, что $VV<=UU$. Также заметим, что для доказательства $UU eq.not VV$ достаточно показать, что функция $VV$ не вогнута в каком-то из направлений $(beta,1), space beta in (-1,1)$, и наоборот, если $VV$ вогнута в соответствующем направлении, то она равна $UU$.
]

#theorem[
    Пусть $f:RR->RR$ --- гладкая функция, такая что:
    + $f$ имеет конечное число корней;
    + $|f(x)| lt.tilde e^((|x|)/delta), space delta>1$;
    + $f$ строго выпукло на $RR$ ($f^(prime prime)(x) >0, space x in RR$).
    Тогда существует такое $epsilon>0$, что $VV^epsilon=UU^epsilon$.
]

#pagebreak()

= Вспомогательные результаты.

#v(1cm)

== Горизонтальная ёлочка.

Пусть функция $m_R$ удовлетворяет дифференциальному уравнению
$
  m_R^prime (u) + m_R (u) = f^prime (u).
$
Пусть $v_R (x,y) = x+1-|y|$ и точки $v_1,v_2 in [-oo,+oo]$. Определим функцию $V_R$ в полосе $Sigma_R [v_1,v_2] = {(x,y) in Sigma | v_R (x,y) in [v_1,v_2]}$:
$
  V_R (x,y) = m_R (v_R)(|y|-1) + f(v_R).
$
\

Аналогично определим функцию $m_L$:
$
  -m_L^prime (u) + m_L (u) = f(u).
$
и $V_L$ в полосе $Sigma_L [v_1,v_2] = {(x,y) in Sigma | v_L (x,y) = x-1+|y| in [v_1,v_2]}$:
$
  V_L (x,y) = m_L (v_L)(1-|y|) + f(v_L).
$

#theorem[ (Теорема 3.1.2 из [2]) Если $m_R^(prime prime) (x)<=0, space x in Sigma_R [v_1,v_2]$, то $V_R$ - диагонально вогнутая функция во всём $Sigma_R [v_1,v_2]$.
]

#theorem[ (Теорема 3.1.3 из [2]) Если $m_L^(prime prime) (x)>=0, space x in Sigma_L [v_1,v_2]$, то $V_L$ - диагонально вогнутая функция во всём $Sigma_L [v_1,v_2]$.
]

#theorem[
    Если $m_R^(prime prime) (x)<=0, space x in Sigma_R [v_1,v_2]$ то
    $
      V_R "вогнута вдоль" (beta,1), space beta in [-1,1] "тогда и только тогда, когда" m_R^prime (x)>=0, space x in Sigma_R [v_1,v_2].
    $
]
#proof[
    Так как $V_R$ - гладкая при $y<0$, вычислим вторую производную по направлению $(beta,1)$ в этой области (по симметричности проверки вогнутости в такой области будет достаточно):
    $
    (partial^2 V_R)/(partial(beta,1)^2) = beta^2 (m_R^(prime prime) (v_R) (-y-1) + f^(prime prime) (v_R)) + 2beta(m_R^(prime prime)(v_R)(-y-1)-m_R^prime (v_R)+ f^(prime prime)(v_R)) + \ + m_R^(prime prime) (v_R) (-y-1) - 2m_R^prime (v_R) + f^(prime prime) (v_R) = \ = -(beta+1)^2y m_R^(prime prime) (v_R) + (beta+1)^2(f^(prime prime) (v_R) - m^(prime prime) (v_R)) - 2 (beta + 1)m^(prime) (v_R) = \ = (beta+1)(-(beta+1)y m_R^(prime prime) (v_R) + (beta-1)m_R^prime (v_R))
    $
    Заметим, что если сократить на $beta+1>=0$, то функция примет линейный вид от $beta$, а значит достаточно проверить ее значения на концах. \
    При $beta = 1$ имеем 
    $
      (partial^2 V_R)/(partial(1,1)^2)<=0 "из условия" m_R^(prime prime)<=0.
    $
    При $beta = -1$ имеем 
    $
      (partial^2 V_R)/(partial(-1,1)^2)<=0 <==>-m_R^prime<=0 <==> m_R^prime >=0.
    $
]

#theorem[
    Если $m_L^(prime prime) (x)>=0, space x in Sigma_L [v_1,v_2]$ то:
    $
      V_L "вогнута вдоль" (beta,1), space beta in [-1,1] "тогда и только тогда, когда" m_L^prime (x)>=0, space x in Sigma_L [v_1,v_2]
    $
]

#remark[
    В обоих случаях, так как $m_R^prime, space m_L^prime$ монотонны, достаточно проверять только неравенства $m_R^prime (v_2)>=0, space m_L^prime (v_1)>=0$. 
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
#align(center)[(Рис. 1: $m_L$ в полосе $Sigma_L [v_1,v_2]$)]

#v(1.5cm)

== Ромб.

Пусть $omega in RR$, введем следующую функцию в ромбе $Sigma_omega = {(x,y in Sigma | |x+y-omega|<=1)}$:
$
  V_omega = alpha(x^2 - y^2)+x(f^prime (omega)-2alpha omega) + C,
$

$
  "где" space alpha = (m_L (omega)-m_R (omega))/4, space C = alpha(1+omega^2)+f(omega)-omega f^prime (omega)
$

#theorem[ (Теорема 3.3.2 из [2])
    Если существует такое число $omega in RR$, что:
    + для $v_R<omega: space m_R^(prime prime)(v_R)<=0, space x in Sigma_R [v_1,omega]$;
    + для $v_L>omega: space m_L^(prime prime)(v_L)>=0, space x in Sigma_L [omega,v_2]$;
    + выполнено уравнение баланса: $m_R (omega)+m_L (omega) = 2 f^prime (omega)$.
    Тогда функция $V$:
    $
      V (v) = cases(V_R (v)";" space v in Sigma_R [v_1,omega]",", V_omega (v)";" space v in Sigma_omega",", V_L (v)";" space v in Sigma_L [omega,v_2].)
    $ 
    диагонально вогнута.
]

#remark[
    Уравнение баланса эквивалентно условию $m_R^prime (omega) = m_L^prime (omega)$.
]

#theorem[
    Пусть выполнены неравенства: 
    + $m_R^(prime)(x)>=0, space x in Sigma_R [v_1,omega]$;
    + $m_L^(prime)(x)>=0, space x in Sigma_L [omega,v_2]$.
    Тогда функция $V$ из теоремы 6 является $D$-вогнутой.
]
#proof[
    Вычислим вторую производную в направлении $(beta,1)$ для функции $V_omega$ и проверим что она неположительна:
    $
      (partial^2 V_omega)/(partial(beta,1)^2)= 2 beta^2 alpha - 2 alpha= 2alpha(beta-1)(beta+1)<=0;
    $
    $
      alpha >=0; space m_L (omega)-m_R (omega)>=0; space m_L^(prime) (omega)+m_R^(prime) (omega)>=0; space m_L^(prime) (omega)>=0 "- следует из условия."
    $
    Таким образом, доказали вогнутость внутри ромба, вогнутость в полосах $Sigma_R [v_1,omega], space Sigma_L [omega,v_2]$ также следует из условия.
    // \ Остается проверить вогнутость на границе ромба, так как там возможен скачок первой производной, по симметричности проверим только для $y<0$. 

    // Рассмотрим сначала часть с $x>=omega$ - нужно проверить следующее:
    // $
    //   (partial V_omega)/(partial(beta,1))<=(partial V_L)/(partial(beta,1))<==> 2 alpha(beta(x-omega)-y)+beta f^prime (omega)<= (beta-1)y m_L^prime (omega) + m_L (omega)beta
    // $
    // Это выражение сразу линейно по $beta$, поэтому проверить необходимо только в крайних точках $beta = plus.minus 1$, а для них неравенство выполняется из диагональной вогнутости $V$. Аналогичная логика работает и для случая $x<=omega$.
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
#align(center)[(Рис. 2: конструкция из теоремы 6 в промежутке $[v_1,v_2]$)]

#pagebreak()

== Вертикальная ёлочка.

Введём гладкие функции $a,b:[0,2]-->RR, space a(0) = lambda =b(0)$ такие, что для всех чисел $l in [0,2]$ выполнены соотношения: 
$
a^prime (l)<0, space b^prime (l)>0;\
b(l)-a(l)=l;\
$
#math.equation(
  block: true,
  numbering: "(1)",
[$(f(b)-f(a))/(b-a) = (f^prime (b)+f^prime (a))/2;$])
$
D_R = f^(prime prime) (b) - (f^prime (b)-f^prime (a))/(b-a) <0, space D_L = f^(prime prime) (a) - (f^prime (b)-f^prime (a))/(b-a) <0;\
m_L (a_0) = m_R (b_0) = (f(b_0) - f(a_0))/2, space a_0 = a(2), space b_0 = b(2).
$

Также определим точку
$
  P(l) = ((a(l)-b(l))/2, l/2 -1)
$
и гладкую функцию $A:[0,2]-->RR$:
#math.equation(
  block: true,
  numbering: "(1)",
[$
    A^prime (l) dot l - A(l) = -(f(a)D_L+f(b)D_R)/(D_R+D_L);\
$])
$
  A(2) = (f(a_0)+f(b_0))/2.
$

Определим $Sigma_(h r b) [a_0,b_0]= Sigma \\ (Sigma_L [-oo,(a_0+b_0)/2] union Sigma_R [(a_0+b_0)/2,oo])$ и функцию $V_(h r b)$ в этой области:
$
  V(x,y) = cases(f(b)+(2(y+1))/l (A(l)-f(b)) "при" x>=(a+b)/2",",
                 f(a)+(2(y+1))/l (A(l)-f(a)) "при" x<=(a+b)/2.)
$
Здесь число $l = l(x,y)$ выбирается таким образом, чтобы точка $(x,y)$ принадлежала отрезку с концами в точках $P(l), space (a(l),-1)$ или в точках $P(l), space (b(l),-1)$. При этом
$
  b = x+y-1, space x>=(a+b)/2; space
  a = x-y-1, space x<=(a+b)/2.
$
Заметим также, что $V(P(l)) = A(l)$.

#theorem[(Теорема 4.2.1 из [2]) Если для функции $f$ существуют функции $a,b,a_0,b_0,A$, которые мы описали выше, то функция $V$, заданная формулой 
$
  V (v)= cases(V_L (v)";" space v in Sigma_L [v_1,(a_0+b_0)/2]",", V_(h r b) (v)";" space v in Sigma_(h r b)",", V_R (v)";" space v in Sigma_R [(a_0+b_0)/2,v_2].) 
$ 
$C^1$ гладкая и диагонально вогнута в области определения.
]
#remark[
    Можно заметить, что функции $a,b$ соответствуют неким параметризациям отрезков $[a_0,lambda], space [lambda,b_0]$, которые вместе задают кривую $l|->P(l)$ из точки $(lambda,-1)$ в точку $((a_0+b_0)/2,0)$, значения функции $V$ на которой и определяет функция $A$.
]

#theorem[
    Функция $V$ из теоремы 8 является $D$-вогнутой, если сужение $f|_([a_0,b_0])$ выпукло.
]
#proof[
    Ввиду симметричности можно считать, что $y<=0, space x>=(a+b)/2$. Выпишем равенства (4.1.10) из [2]:
    $
      a^prime_x = a^prime_y, space b^prime_x = b^prime_y = 1, space l^prime_x = l^prime_y = 1+D_R/D_L.
    $
    Введём $I = 1/l (A(l)-f(b))$, и заметим что $I^prime_x = I^prime_y, space I^(prime prime)_(x x) = I^(prime prime)_(x y) = I^(prime prime)_(y y)$. Теперь вычислим вторую производную в направлении $(beta,1):$
    $
       (partial^2 V_omega)/(partial(beta,1)^2) dot (beta^2 + 1) = beta^2(f^(prime prime) (b)+2(y+1)I^(prime prime))+2beta(f^(prime prime) (b)+2(y+1)I^(prime prime) + 2I^prime) + f^(prime prime) (b)+2(y+1)I^(prime prime) + 4 I^prime = \ =(beta+1)^2 (f^(prime prime) (b)+2(y+1)I^(prime prime)) + 4(beta+1)I^prime.
    $
    Опять же, если сократить на $beta+1>=0$ выражение станет линейным по $beta$ и для $beta=1$ неравенство будет следовать из диагональной вогнутости функции $V$. Проверим в случае $beta = -1$:
    $
      I^prime <=0 <==>(l(A^prime (l) dot (1+D_R/D_L) - f^prime (b)) - (1+D_R/D_L)dot (A(l)-f(b)))/(l^2)<=0.
    $
    Можем считать, что $l eq.not 0$, так как вогнутость в этой точке будет следовать из вогнутости по всем точкам в некоторой её окрестности. Тогда можем упростить, воспользовавшись равенствами (1) и (2):
    $
      - (1+D_R/D_L) dot (f(a)D_L+f(b)D_R)/(D_R+D_L) - l dot f^prime (b)+(1+D_R/D_L)dot f(b)<=0 <==>f(b)-f(a)-f^prime (b) (b-a)<=0 <==>\ <==>f^prime (b)>= f^prime (a) - "следует из условия" f^(prime prime)>0
    $ 
    Полученное неавенство при $x<=(a+b)/2$ симметрично в смысле перестановки $a$ и $b$ и изменения знаков первых производных. Тогда соответствующее условие $D$-вогнутости имеет вид
    $
      -f^prime (a)>= -f^prime (b)," что эквивалентно первому случаю."
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
#align(center)[(Рис. 3: конструкция из теоремы 8 в промежутке $[v_1,v_2]$)]

#v(2cm)

== Склейка основных конструкций.

#definition[(определение 1.5.2 из [2])
    Пусть $G: Sigma -> RR$ — диагонально вогнутая функция. Будем говорить, что функция $G$ экстремальна относительно направления $(1,1)$ в точке $x$, если точка $x$ является концом некоторого отрезка $ell$, второй конец которого лежит на границе множества $Sigma$, отрезок $ell$ параллелен направлению $(1,1)$, ограничение $G|_ell$ является аффинной функцией, а функция $G$ дифференцируема в направлении $(1,1)$ в точке $x$.

    Определение функции, экстремальной относительно направления $(1,-1)$, формулируется полностью аналогично.
]

#theorem[(теорема 1.5.3 из [2])
    Пусть $G: Sigma -> RR$ — полунепрерывная сверху диагонально вогнутая функция, множество точек разрыва которой дискретно. Пусть также существует число $epsilon > 1$, такое что $abs(G(x)) <= e^(abs(x_1)/epsilon)$
    для всех $x in Sigma$.
    Предположим, что для любой точки $x$ из внутренности множества $Sigma$ выполняется одно из следующих условий:
    + функция $G$ билинейна в некоторой окрестности точки $x$;
    + функция $G$ аффинна относительно направления $(1,1)$ и экстремальна относительно направления $(1,1)$ в точке $x$;
    + функция $G$ аффинна относительно направления $(1,-1)$ и экстремальна относительно направления $(1,-1)$ в точке $x$;
    + функция $G$ экстремальна одновременно относительно направлений $(1,1)$ и $(1,-1)$ в точке $x$.\
    Тогда $G eq.triple VV$.
]
#remark[
    Легко видеть, что склеенные по кускам с $V_L, V_R$ углы, ромбы и ёлочки удовлетворяют этой теореме.
]

#theorem[(Теорема ??? из [1])
    Для гладкой функции $f$, удовлетворяющей условиям 1), 2) теоремы 1, существует такое $epsilon_0>0$, что для полосы $Sigma^epsilon, space epsilon<=epsilon_0$ функция $VV^epsilon$ получается путём склеивания конструкций из теорем 7 и 8, которые пересекаются только по горизонтальным ёлочкам.
]

#theorem[(Теорема ??? из [1])
    Для гладкой функции $f$, удовлетворяющей условиям 1), 2) теоремы 1, все числа $lambda_i$, соответствующие вертикальным ёлочкам в построении $VV$, в точности являются корнями $f^(prime prime prime)$, такими что $f^(prime prime prime) (lambda_i-epsilon) > f^(prime prime prime) (lambda_i+epsilon)$.
]
#remark[
    В достаточно малой полосе достаточным условием для $D$-вогнуточти в вертикальной ёлочке будет условие $f^(prime prime)>0$ во всех таких точках $lambda_i$.
]
#proof[ 
    действительно, это условие значит, что в некоторой окрестности $lambda_i$ вторая производная $f$ также положительна, а значит можно выбрать такое $epsilon>0$, что $a_0,b_0$ будут пренадлежать этой окрестности. По теореме 9 имеем искомое. 
]

#theorem[
    Обозначим за $VV_f$ максимальную диагонально вогнутую функцию $f$, пусть $g$ - линейная функция, тогда $VV_(f+g)=VV_f+g$.
]

#v(2cm)

= Доказательство основного результата.

#v(1cm)

#counter("theorem").update(0)

#proof[ (Теоремы 1)  #h(1cm)
    Проверим $D$-вогнутость функции $VV^epsilon$, структура которой описана в теореме 11. В силу теоремы 9 функция $VV^epsilon$ $D$-вогнута во всех вертикальных ёлочках. Остается проверить только значения $m^prime_R = m^prime_L$ в крайних точках. 
    Легко видеть, что в $VV^epsilon$ вертикальные ёлочки и ромбы чередуются. Пусть вертикальным ёлочкам с $lambda_i$ соответствуют крайние точки $c_i = (a^i_0+b^i_0)/2$, тогда по замечанию 2 достаточно проверить выполнение условия только в точках $c_i$ и $plus.minus oo$. Рассмотрим $m_R^prime (c_i) = m_L^prime (c_i)$:
    $
      m_R^prime (c_i) = f^prime (c_i) - m_R^(prime prime) (c_i) >= f^prime (c_i)
    $
    Обозначим $M=max f^prime (lambda_i)$, пусть функция $g=f+(M+1) x$. По теореме 13 $D$-вогнутость функций $VV_f$ и $VV_g$ эквивалентны, значит можем считать $f=g$. Легко видеть, что $g$ удволетворяет всем условиям теоремы, а также $g^prime (lambda_i)>0$. Так как расстояние между $c_i$ и $lambda_i$ линейно зависит от $epsilon$, можем считать что $epsilon$ достаточно мало, что $f^prime (c_i)>0$.\

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
    Рассматривая $m_L$ в $[-oo,v_2]$ и $m_R$ в $[v_1,+oo]$ можно понять, что:
    $
      lim_(u-->+oo) m_R^prime (u) = lim_(u-->+oo) e^(-u) integral_(v_1)^u e^t f^(prime prime) (t) d t >=0,\
      lim_(u-->-oo) m_L^prime (u) = lim_(u-->-oo) e^(u) integral_(u)^v_2 e^(-t) f^(prime prime) (t) d t>=0
    $
    по выпуклости $f$. Таким образом проверили знак $m_R^prime = m_L^prime$ на всех крайних точках.
]

#align(center,  canvas({
  scale(2)

  line((-4, 1), (5, 1))
  line((-4, -1), (5, -1))

  line((-4, 0), (5, 0), stroke: 0.3pt)
  line((0, -1.4), (0, 1.8), stroke: 0.3pt)

  content((5.1, 0.05), [$x$])
  content((0.15, 1.95), [$y$])

  content((-2.0, -1.2), [$c_1$])
  content((3.0, -1.2), [$c_2$])

  content((-1.0, 0.2), [$m_R$])
  content((2.0, 0.2), [$m_L$])

  content((-3.0, -1.2), [$a^1_0$])
  content((2.0, -1.2), [$a^2_0$])
  content((-1.0, -1.2), [$b^1_0$])
  content((4.0, -1.2), [$b^2_0$])

  line((-1.0, 1), (-2.0, 0))
  line((-1.0, -1), (-2.0, 0))
  line((-3.0, 1), (-2.0, 0))
  line((-3.0, -1), (-2.0, 0))

  line((0.5, 1), (-0.5, 0))
  line((0.5, -1), (-0.5, 0))

  line((0.5, 1), (1.5, 0))
  line((0.5, -1), (1.5, 0))

  line((2.0, 1), (3.0, 0))
  line((2.0, -1), (3.0, 0))
  line((4.0, 1), (3.0, 0))
  line((4.0, -1), (3.0, 0))
}))
#align(center)[(Рис. 4: чередование вертикальных ёлочек и ромбиков в $VV^epsilon$ из доказательства теоремы 1)]

#v(4cm)

= Список литературы.
[1] Paata Ivanisvili, Dmitriy M. Stolyarov, Vasily I. Vasyunin, Pavel B. Zatitskiy, #emph("Bellman Function for Extremal
Problems in BMO II: Evolution"), September 2018\
[2] Dmitriy Stolyarov, Vasily Vasyunin, Pavel Zatitskii, #emph("Martingale transforms of bounded random variables and indicator functions of events"), October 5, 2023

