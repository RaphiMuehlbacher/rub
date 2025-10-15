# Rub Programming Language

A statically typed, interpreted programming language with type inference, built in Rust.

## Features

* Static Typing with Type Inference: Type system with automatic type inference
* Expression-Based Syntax: Automatic return of last expression when no semicolon is present
* First-Class Functions: Functions are values that can be passed around and returned
* Closures: Functions automatically capture their surrounding environment
* Structs: Custom data types with typed fields
* Vectors: Built-in dynamic arrays with type parameter support `Vec<T>`
* Control Flow: if expressions, while loops
* Method Calls: Extensible method system on built-in types
* Built-in Functions: print(), clock()
* Data types
    - `Int` - 64-bit integers
    - `Float` - 64-bit floating point numbers
    - `String` - UTF-8 strings
    - `Bool` - Boolean values
    - `Vec<T>` - Dynamic arrays
    - struct - Custom data structures
    - Function types with full type signature
    - `nil` - Null value

## Example Programs

#### Hello World

```
print("Hello, World!");
```

#### Variables and Functions

```
let x = 42;
let y = 3;

fn add(a: Int, b: Int) -> Int {
    a + b
}

print(add(x, y));
```

#### Structs

```
struct Point {
    x: Int,
    y: Int,
}

let p = Point { x: 10, y: 20 };
print(p.x);
p.y = 30;
```

#### Control Flow

```
let i = 0;
while i < 10 {
    if i == 5 {
        print(i);
    }
    i = i + 1;
}

for(let i = 0; i < 10; i = i + 1) {
    if i == 5 {
        print(i)
    }
}

```

#### Closures

```
fn makeCounter() {
    let count = 0;
    fn() {
        count = count + 1;
        count
    }
}

let counter = makeCounter();
print(counter());  // 1
print(counter());  // 2
```

#### Vectors

```
let nums = [1, 2, 3, 4, 5];
nums.push(6);
print(nums.len());
```

#### Project Structure

- lexer.rs - Tokenization
- parser.rs - AST generation
- ast.rs - Abstract Syntax Tree definitions
- ast_lowerer.rs - AST to IR conversion
- ir.rs - Intermediate Representation
- resolver.rs - Name resolution
- type_inferrer.rs - Type inference engine
- interpreter.rs - Tree-walking interpreter
- method_registry.rs - Method dispatch system
- builtins.rs - Built-in functions
- error.rs - Error types and reporting

#### Implementation Details

- Tree-walking interpreter with environment-based scoping
- Hindley-Milner-style type inference with type variables
- Reference counted variables (Rc) for shared ownership
- `DefMap`: Maps variable definitions to their declaration sites
- `ResolutionMap`: Tracks name usage and links to definitions
- Span tracking throughout compilation for precise error locations
- Miette for beautiful error reporting