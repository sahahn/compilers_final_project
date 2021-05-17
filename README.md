# Compilers Final Project
Sage Hahn

My implementation focused on implementing both a lambda function with lexical scoping as well as in the same compiler an alternate function called 'dynam', with simmilar function to lambda, but dynamic scoping (variables passed at the time the function is called). I'll discuss below some key pieces of the implementation and how they varied between lambda and dynam.

### Type Checking

Type checking for the introduced lambda expression was fairly straightforward, with really only a new case for the definition of the Lambda expression - where the basic idea is just to type check the body of the lambda given the current environment + the defined types from the definition, from here the output type of the lambda expression can be inferred. 

Type checking for the dynam expression was in contrast much more complicated / convoluted. The idea was I wanted to type check every call to a defined dynam expression, as the environmental variables might change from call to call, and I wanted to enforce the constraint that all calls to the dynam function must both type check and return the same type, e.g., see rt_error1. To do this I had to enforce a constraint on the usage of dynam to be directly associated with a variable. Then, when type checking for Let, there is a sub case for dynam where the definition of the dynam is passed along in another env recursively to the body of the Let statement, where whenever a call to the assigned variable / dynam occurs, the passed along definition is evaluated in the current context. The type checked statement is saved in the environment as well, to be assigned once the body is type checked. There are a number of other smaller implementation details, but suffice to say, the implementation ended up feeling brittle / hacky and bit too specific. 

### Uniquify

The premise of the dynam statement working is that if a closure argument within a dynam expression is changed, that should be reflected when that dynam expression is next called. In the basic uniquify implementation for lambda, where just the arguments are made unique, this would not work, as for example:

    let x = 1 in
    let f = dynam y: Integer -> x + y
    in f(2) + let x = 2 in f(2)

Would become

    let x_1 = 1 in
    let f_2 = dynam y_3: Integer -> x_1 + y_3
    in f_2(2) + let x_4 = 2 in f_2(2)

Where importantly x_1 and x_4 are two different variables, so changing x_4 wouldn't
influence calls to the dynam function. Instead, in order to make this work, we store the referenced closure args for every dynam in both the DynamTE definition, but also in every call a dynam function. Then in uniquify the closure args within the body are replaced with new variables, closure_var_x, closure_var_y, etc... and the new closure args saved with the definition (in the same order).

So now the example before is

    let x_1 = 1 in
    let f_2 = dynam y_3: Integer -> closure_var_5 + y_3
    in f_2(2) + let x_4 = 2 in f_2(2)


### Convert To Closure

If a lambda definition is encountered, then it is converted into a closure, and a new function definition added (convert to closure recursively called on the body, then a new function definition added, with an extra vector type argument for all of the closure vars, then at the top of the def, the vector is 'unpacked' and set to variables). Then the Lambda definition is replaced with a vector containing first element function reference and second element the current closure args. Then, when a reference to the lambda definition is called, the function call is replaced with a reference to the first element of the closure, calling the base arguments + the second element of the closure arguments. The tricky part here is making it work with if the lambda was saved to a variable, or if called directly (test4). 

In contrast, the case for the dynam definition occurred only as a sub-case of Let, where as with the lambda case, the body of the expression is saved as a new function, but instead of replacing it with a closure, just the name of the new function is returned, and then passed recursively to the body of the let, ultimately replacing the let with just the body of the dynam. Then within the recursive calls to the body, if a dynam function is referenced, then it will be replaced with a new function call to saved function name, and passed the original arguments, plus the current closure arguments, where making sure the correct closure vector of arguments is both passed and set in the definition is the slightly tricky part.

### Flatten Lambda

In the convert to closure pass above, I ran into an issue where my implementation didn't work in the case of something like test5:

    let f = let x = 5
    in lambda y: Integer -> x+y
    in f(5)

Where f couldn't be saved directly as a closure, as it was associated with first a let expression. To address this I added a pass
which 'flattens' these statements, by essentially converting the above statement to:

    let f = lambda y: Integer -> let x = 5 in x+y
    in f(5)

That said, there are almost certainly still cases I am missing which this pass could catch.


### Other Passes

Most other passes just involved adding new recursive cases for DynamTE and LambdaTE, without any new special cases.

### Things that didn't work

There were certainly a lot of things I wish I had time to address, but couldn't end up get working. These are mostly related to the dynam function and are a directly result of both the brittle-ness of the implementation and the inherent problems of dynamic scope. These are included under the tests folder under should work, and basically just highlight a problem where the dynam implementation explodes and doesn't work in the case of complicated nested expressions in the dynam definition.

### Takeaway on lambda vs dynam

I am thoroughly convinced on the merit of lexical scoping, both from an implementation and usage perspective. 

### Test Cases

In the tests folder there are a few different types of tests, where tests 1-8 are run as usual by calling the modified run_tests.py script. Then there are a few different test cases provided, e.g., as_error1 which is designed to produce an assertion error. Likewise, rt_error1 and rt_error2 are designed to produce a RuntimeError (in all these cases the errors are from type checking things you can't do). Then I provide two examples under should_work 1 and 2 that represent cases that really should work, but that I didn't get to fixing the implementation to make work.