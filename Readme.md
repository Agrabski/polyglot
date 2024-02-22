# Polyglot

An cross-platform, cross-language interpreter of simple, parametrizable logical expression in Reversed Polish Notation.

## The motivation

Currently, there really isn't a way to share a simple piece of parametrized logic between frontend, and backend code.
Let's say, for instance, that you wanted to display data in a list, with actions that the users can perform on a row.
The user may, or may not have permissions to perform an action and we want to grey-out the unavailable actions.
One way to solve that problem, would be to contaminate the list data, with names of actions that the user can take, for each row, which were evaluated on the backend.
But what if generating the definition of that list, is expensive?
How do you validate that the user trying to perform an action on a row, has permission to do so?

One way to solve that problem, would be to attach a logical expression, to the action definition, that would determine whether the user had permissions to execute it.
If that expression would be executable by both frontend and backend, frontend could use it to grey-out unavailable actions and backend could use it to validate permissions (given that the expression was cryptographically signed).
Thats where polyglot comes in.

## The package

This package provides a compiled interpreter of a simple language to express logical expressions, that can accept parameters.
It is compiled to a native binary, as well as to webassemby, with bindings for several programming languages (currently: Rust, C\# and javascript).

### Language

The language interpreted by polyglot is essentially constructed from boolean operators and comparison operators written in a Lisp-like Reversed Polish Notation
For example: `(= @a 1)` means 'parameter with name a is equal to 1'.
Comparison expressions can be also combined with boolean operators.
For example `(& (= @a 1) (= @b 'abc'))` means 'parameter a is equal to 1 and parameter b is equal to string "abc"'.
Boolean operators accepts any number of subexpressions as argumetnts.
For example `(| (= @a 1) (= @b 'abc') (! @c g))`.

Boolean operators:
- `&` and
- `|` or

Comparison operators
- `=` equal
- `!` not equal
- `>` first operand greater than second (only numeric values) (not implemented yet)
- `>=` first operand greater or equal than second (only numeric values) (not implemented yet)

Numeric values can be specified in `'` or as bare strings: `123` equivalent to `'123'`.

Parameters can be accessed using `@`

[Interpreter implementation file](polyglot/src/lib.rs), contains unit tests with additional expression examples.
