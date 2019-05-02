---
layout:     post   				    # 使用的布局（不需要改）
title:      DP and Recursion			# 标题 
subtitle:   A little thought about Lambda Calculus #副标题
date:       2019-02-17			# 时间
author:     DHZ 						# 作者
header-img: img/draw-recursive.jpg	#这篇文章标题背景图片
catalog: true 						# 是否归档
tags:								#标签
    - functional programming
    - lambda calculus
    - programmimng
    - Haskell
    - Scala
    - Dynamic Programming
---



# Functional or imperative ? — DP and Recursion

From the point of view of mathematics, DP and recursion are doing the same thing. More precisely, they are different program implementations of same mathematical solution. 

Let’s take **Fibonacci**, the example that is always be the very first one to demonstrate DP or recursion.The definition of **Fibonacci sequence** is 

~~~
fib(0) = 1
fib(1) = 1
fib(n) = fib(n-1) + fib(n-2)
~~~

*(Since we’re interested in recursion, not in the nature of Fibonacci numbers, this post will ignore the matrix form of computing Fibonacci numbers using linear algebra.)*

If we just implement it by the definition, the program would be

~~~scala
val fib: Int => Int = n =>
    if (n <= 1) 1
    else
      fib(n - 1) + fib(n - 2)
~~~

in *Scala* or

~~~haskell
fib 0 = 1
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
~~~

in *Haskell*

Then you will observe that when calculating every $fib(n)$ , there are $$2n$$ calls of $$fib$$ , but only $$n$$ of them are different, *e.g.* $$fib(5) = fib(4) + fib(3)$$ and $$fib(4) = fib(3) + fib(2)$$ . $$fib(3)$$ is called **twice** in calculating $$fib(5)$$ . By careful calculation, you will find that the running time of the naive recursion is exponential. That’s why we need to use **Dynamic Programming**, *e.g.*

~~~scala
val fib: Int => Int = n => {
    val dp = new Array[Int](n + 1)
    dp(0) = 1
    dp(1) = 1
    for (i <- 2 to n)
      dp(i) = dp(i - 1) + dp(i - 2)
    dp(n)
  }
~~~

or maybe a more clever way, since we only need to know $$fib(n-1)$$ and $$fib(n-2)$$ to calculate $$fib(n)$$ 

~~~scala
val fib: Int => Int = n => {
    val dp = Array.fill[Int](2)(1)
    for(i <- 2 to n){
      	/* dp = [fib(i-2), fib(i-1)] */
        val temp = dp(1)
      	dp(1) = dp(0) + dp(1) /* dp(1) = fib(i) */
        dp(0) = temp /* dp(0) = fib(i-1) */
      }
    }
~~~

in *Scala* 

Then you might think **“Like I said! how can they be equivalent! DP has linear running time here!”**
Actually, it is really simple to make them be equivalent, when we have a **cache** to preserve those interim results. 

A naive attempt could look something like this:

~~~scala
val cache = new mutable.HashMap[Int,Int]

val fib: Int => Int = n => {
  if(cache.contains(n)) cache(n)
    else{
      var temp = 0
      if(n <= 1) temp = 1
      else temp = fib(n-1) + fib(n-2)
      cache(n) = temp
      temp
    }
~~~

So theoretically, recursion is equivalent to DP if we add a **cache** to it. Though there are still some problems with this nifty implementation, it indeed turns the fib that ran in **exponential** time into a fib which runs in **linear** time.

One problem is that it complicates our implementation of `fib`, the other one is that the cache sticks around after the function is finished running. For `fib`, this is not a problem, but for some algorithms it would be. 

## Let’s leave the problems to talk later and switch to *Haskell* now. 

In purely functional language like *Haskell*, it becomes tricky to write DP, since you don’t have mutable variable and loop, but you can still do it by making use of the evaluation strategy called  **Lazy Evaluation**, which means that when a value is needed, it is calculated, and kept ready in case it is asked for again. If we define some list, `xs=[0..]` and later ask for its 100th element, `xs!!99`, the 100th slot in the list gets *"fleshed out"*, holding the number `99` now, ready for next access.

So the implemetation would be

~~~haskell
fib = (fibs !!)
    where fibs = 1 : 1 : zipWith (+) fibs (tail fibs)
~~~

The trick is to cause the list to get created, and cause the list not to go away (by way of garbage collection) between calls to `fib`. The easiest way to achieve this, is to *name* that list. **"If you name it, it will stay."** 

A better solution is to write a `memo`function to encapsulate the memoization logic. Let’s imagine we already have our magical `memo` combinator available. How would we use it? The first instinct might be something like this.

~~~haskell
memo_fib = memo fib
	where fib 0 = 0
		  fib 1 = 1
		  fib n = fib (n-1) + fib (n-2)
~~~

While that certainly does something, it doesn’t do what we want it to do.The problem is that our `fib` function isn’t aware that there exists a memoized version of it so even if we cache it’s return value, it doesn’t access that cache. It just recursively calls itself. After thinking a bit about this, we might come up with this version, which will be correct and you can also easily extract a memo out by carefully making use of the **lazy evaluation mechanism**.

~~~haskell
memo_fib = memo fib'
    where fib' 0 = 1
          fib' 1 = 1
          fib' n = memo_fib (n - 1) + memo_fib (n - 2)
          
memo f = (map f [0..] !!)
~~~

Or we can define a clever `open_fib` to make it use 'open recursion' rather than call itself directly.

~~~haskell
open_fib :: (Int -> Int) -> Int -> Int
open_fib memo_fib 0 = 1
open_fib memo_fib 1 = 1
open_fib memo_fib n =  memo_fib (n-1) + memo_fib (n-2)
~~~

You can get unmemoized `fib` by using `fix open_fib`  where `fix f = let {x = f x} in x`, which means that `fib` is the minimal fix point of the high-order function `open_fib`. We call the high-order function that produces a fix point of a function fix-point combinator.

Let’s expand the `fix open_fib` to explain what happens:

~~~haskell
-- fix f = let {g = f g} in g
fix open_fib
= open_fib (fix open_fib)
= (\rec n -> if n <= 1 then 1 else rec (n-1) + rec (n-2)) (fix open_fib)
= \n -> if n <= 1 then 1 else fix open_fib $ (n-1) + fix open_fib $ (n-2)
= \n -> if n <= 1 then 1
    else (if n - 1 <= 1 then 1 else fix open_fib $ (n-2) + fix open_fib $ (n-3))
        +(if n - 2 <= 1 then 1 else fix open_fib $ (n-3) + fix open_fib $ (n-4))
= \n -> if n <= 1 then 1
    else (if n - 1 <= 1 then 1 else 
                               if n - 2 <= 1 then 1 else
                                                    ...)
        +(if n - 2 <= 1 then 1 else
                               if n - 3 <= 1 then 1 else
                                                    ...)
~~~

Notice that the use of `fix` allows us to keep "unravelling" the definition of `open_fib`: every time we hit the `else` clause, we product another copy of `open_fib` via the evaluation rule `fix open_fib = open_fib (fix open_fib)`, which functions as the next call in the recursion chain. Because of the **Lazy Evaluation Mechanism**, `open_fib` would only evaluate the `fix open_fib` inside if it is needed, otherwise if the argument `n`of `open_fib (fix open_fib)` is 1 or 0 , then it would just return 1. So eventually we hit the `then` clause and bottom out of this chain.

Then we are prepared to define the `memo` combinator, which is a fix point combinator like `fix` , but generating a memoized `memo_fib`  from `open_fib` , which can be used in the intuitive way.

~~~haskell
memo :: ((Int -> Int) -> Int -> Int) -> Int -> Int
memo f = memo_f
   where memo_f = (memoList !!) 
         memoList = map (f memo_f) [0..]
        
memo_fib = memo open_fib
~~~

It only difference between `memo` and `fix` is that, we add a list to preserve the intermediate values.

There are two things we can do better. Firstly, the type of our `memo` function is  `((Int -> Int) -> Int -> Int) -> Int -> Int`. This means it’s not generic. Secondly, this `memo`implementation is still too slow. It requires a traversal of the cache list every time we want to get a value out because lists have linear time indexing. The complexity of our `memo_fib` function is quadratic or so.To avoid the linear access time in our structure, we can use a binary tree instead of a list. Trees have nice, logarithmic time, access properties that we want.

All implementations of memo combinator above highly depends on Haskell’s **Denotational semantics**, or more concretely,  **Lazy Evaluation mechanism**. 

## How do we abstract the memoization logic in an imperative way to solve the problems mentioned above?

Here’s what my first trial:

~~~scala
var fib: Int => Int = n =>
    if (n <= 1) 1
    else
      fib(n - 1) + fib(n - 2)

val memorize:(Int => Int) => Int => Int = f => {
  val cache = new mutable.HashMap[Int,Int]
  new Function[Int,Int] {
    def apply(arg: Int): Int ={
      if(cache.contains(arg)) return cache(arg)
      val temp = f(arg)
      cache(arg) = temp
      return temp
    }
  }
}

fib = memorize(fib)
~~~

It seems prefect, but there is a trap. If we change the name of function on line 18 from `fib` to `memo_fib`, the `memo_fib` would be a fake `memo_fib` which is unmemoized. The reason is that the `fib` in `memorize` is still the **uncached** ` fib`, not `memo_fib`.

The situation is really the same as we met in writing the Haskell version **memo combinator**. We saw two solutions, one is to make the fib to call the `memorize fib`  in `memorize` function,  another is that to define an open recursive version of `fib`and generates `memo_fib` directly by applying a fix point combinator `memo` on it. 

The first solution is easy to implement

~~~scala
var fib : Int => Int = memorize(n => if (n <= 1) 1 else fib(n-1) + fib(n-2))
~~~

Since in most of imperative programming language, the evaluation strategy would be strict which means an expression is evaluated as soon as it is bound to a variable,  the fix point combinator we used in `Haskell` is not working anymore.

We need to try the second solution with another fix point combinator that works in strict programming language, called

##  Y-Combinator

In order to achieve our objective of “capturing the essence of recursion in a function”, is to write this Fibonacci function without referring to the function in its own body. To put this another way, we’re going to look for an implementation which would let us write Fibonacci as an anonymous function, like this:

~~~scala
n => {
  if (n <= 1) return 1;
/* Problem: we have no name for ourselves that we can use here */
  return ???(n - 1) + ???(n - 2);
}
~~~

We can make a similar definition like what we did in *Haskell*

~~~scala
val genFib :(Int => Int) => Int => Int = fib => n =>
  if (n <= 1) 1
  else fib(n - 1) + fib(n - 2)
~~~

Obviously, this is not `fib` function, but  if we call `genFib` with a `fib`, that we’ll get the`fib` that we want out of it. But there is the problem: The way we get the `fib` is by calling `genFib` with some argument:

~~~scala
val fib = genFib(?)
~~~

But the missing argument `fib` is the `fib`  itself, which we can only get as the output of `genFib`:

~~~scala
val fib = genFib(genFib(?))
~~~

Which makes us need to write:

~~~scala
val fib = genFib(genFib(genFib(?)))
~~~

etc. We’re trapped in an infinite chain here; we need some way to “close the loop.”
The y-combinator does this loop-closing. It is a fix point combinator which take `genFib` as an argument and return the minimum fix point of `genFib` which is the `fib` we want.

Since we have this idea, things becomes easier. We are sure that the `yCom` would look like this:

~~~scala
val yCom = genFib => genFib(f)
~~~

f is the result function we want, so we just expand f

~~~scala
val yCom = genFib => genFib(n => yCom(genFib)(n))
~~~

And we finished.

~~~scala
val genFib :(Int => Int) => Int => Int = fib => n =>
  if (n <= 1) 1
  else fib(n - 1) + fib(n - 2)

/* actually we can define yCom in type ((a => b) => a => b) => a => b, but in scala */
/* we cannot make arrow function generic. You can define a generic yCom using def keyword.*/
val yCom:((Int => Int) => Int => Int) => Int => Int = 
	gf => gf(n => yCom(gf)(n))

val fib = yCom(genFib)
~~~

Let’s break down how this works.

When we call `fib n`, we’re calling the `genFib` function returned by `yCom`. if  `n <= 1` then it will just return 1. If `n > 1 `, `genFib` will create new function called `yCom(gf)` and call `yCom(gf)(n-1)` and `yCom(gf)(n-2)`, which is equivalent to call `fib(n-1)` and `fib(n-2)`. This is exactly the behaviour we want. 

The Y-combinator encapsulates the essence of recursion, so we can modify it to make a `yComM` which provides a *recursion which is memoized using a cache*.

~~~scala
val yComM: ((Int => Int) => Int => Int, mutable.HashMap[Int, Int]) => 
      Int => Int = (gf, cache) =>
    gf { n =>
      if (cache.contains(n)) cache(n)
      else {
        val temp = yComM(gf, cache)(n)
        cache(n) = temp
        temp
      }
  }

val genFib: (Int => Int) => Int => Int = fib =>
    n =>
      if (n <= 1) 1
      else fib(n - 1) + fib(n - 2)

val memo_fib = yComM(genFib, new mutable.HashMap[Int, Int]())

~~~

