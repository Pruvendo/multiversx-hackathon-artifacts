# Pruvendo team’s MultiversX Hackathon artifacts repo

We in Pruvendo use the formal methods where verification is performed by mathematical methods (roughly speaking, a code correctness is proved as a theorem).

  

Briefly, the verification process can be splitted into the following phases:

+   Specification - before any verification it’s needed to state what it’s planned to verify. This part can be divided into the following sections:
    + Business-level specification (high-level description intended for the end-users of the smart contract system)
    + Property-level specification (description of all the properties of the system in a natural language)
    + Intermediate-level specification (description of all properties in a language understandable by software developers)
    + Low-level specification (description of all properties with Coq-specific predicates, intended for verifiers only). This activity is typically done when the next part - Translation - is completed
    

-   Translation as conversion of the Rust code into a set of functions with provable properties. The process has two stages:
    + Translation from Rust into Coq-based DSL called Ursus
    + Translation from the intermediate representation mentioned above into a set of functions
    

-   Verification as supplying evidence of correctness of low-level specification towards the set of functions received above is conducted by deductive software verification.
    

  

## Repo parts description
This repo contains parts of our work for the hackathon which can be disclosed

  

### 1.  Translator from Rust (MultiversX) to Ursus language. (/Rust-Ursus-Translator)

What is it?  Translator transforms Multiversx contracts to our language Ursus. Why is it needed?  Translator is needed for expressing Rust contract in Ursus, which we use as a foundational part of our formal verification work.

Translation works in two steps - receiving Rust AST from a contract file and transforming AST into language constructions of Ursus (listing of Ursus code). More technical details you can see (there)[Rust-Ursus-Translator/README.md]. Writing translator via using Coq toolchain is used because there are convenience of constructing syntax expression via inductive types and convenience of handling syntax tree.

  

As for now, we translate following constructions:

-   Storage Mappers
    
-   Functions with return expressions
    
-   Constants
    
-   Consider function calling without complex boolean and etc expression in arguments
    
-   Function manipulating semi-primitive types (integer, boolean, couple types from stdlib - Option, String)
    

But at the moment translator has following limitations:

-   Variable declaration strictly needs to have explicitly written type (in ‘let…’ construction). And ‘let’ construction can’t be last statement in a block of code (function body)
    
-   Translator can’t process code, which was written in functional style
    
-   Storage-mapper's API is limited
    

  
  

### 2.  Translated Adder contract (/Adder-Verification)
    

Translated Adder contract from MultiversX examples: [link](https://github.com/multiversx/mx-sdk-rs/blob/master/contracts/examples/adder/src/adder.rs)

Translation has been done automatically using Translator from (1).

We’ve supported limited API for SingleValueMapper, VecMapper and UnorderedSetMapper, which is used in Adder and CrowdFunding contracts

  

Noticeable constructions:

-   Storage-mapper usage
    
-   Closure in SingleValueMapper’s “update” method
    

  

### 3.  Translated Crowdfunding contract (/Crowdfunding)
    

Translated Crowdfunding contract from MultiverX examples: [link](https://github.com/multiversx/mx-sdk-rs/blob/master/contracts/examples/crowdfunding-esdt/src/crowdfunding_esdt.rs)

Translation has been done by hand, as not all construction of MultiversX Rust are supported in Translator (for now).

Constructions which support have been added to Ursus, besides the ones mentioned in (1) are:

-   “match” construction
    
-   solid piece of Blockchain and CallValue APIs
    
This contract is accompanied with the [high-level specification](./Crowdfunding/spec/Crowdfunding.md) that claims all the statements to be proven during the process of the formal veirication.  

### 4.  Library for Rust/Multiversx VM (/RustVM)
    

Our library of MultiversX Rust types and VM-related functions. We’ve implemented support for Rust’s integer types (signed and unsigned), RandomnessSource and its API, couple types from stdlib (Option, Vec, String) and a bunch of Blockchain and CallValue APIs

  

### 5.  Tool for making AST from Rust contracts, written in Rust (/RustAST)
