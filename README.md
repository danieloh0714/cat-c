# LLVM Compiler Transformations
An LLVM compiler has three components: the front-end, the middle-end, and the back-end.
The front-end converts any programming language into an intermediate representation (IR).
The middle-end runs a bunch of optimizations on the IR to make the code more time/space efficient.
The back-end converts the IR into assembly language for the computer.

![diagram](https://www.aosabook.org/images/llvm/LLVMCompiler1.png)

Using C++ and the [LLVM library](https://llvm.org/docs/index.html), I built a simple optimization in the middle-end (IR) of the LLVM compiler.
I used techniques such as constant propagation, constant folding, etc. to make compiled code run faster by removing computational redundancies from the code.
