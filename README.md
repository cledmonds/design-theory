# Combinatorial Design Theory 

## Overview

This repository contains a formalisation of combinatorial design theory using Isabelle/HOL. It is intended as a general library which can be used for any future formalisations involving designs, or similar structures such as hypergraphs. 

## Combinatorial Designs

Combinatorial Design theory is an area of mathematics investigating incidence set systems with certain structural properties - such as balance and symmetry. At their core, a design is a pair (V, B) where V is a finite set of points and B is a collection of subsets of V. 

There are many different types of designs. This formalisation includes the following: 
- Block Designs
- t-wise balanced designs
- pairwise balanced designs (PBD)
- Designs with constant replication number
- t-designs
- t-covering and t-packing designs
- BIBD's
- Symmetrical BIBD's
- Group Divisible Designs (GDD)
- Triple Systems
- Resolvable Designs

In some settings, designs and hypergraphs can be used interchangeably. In fact, it's very common for hypergraphs to be used within design theory proofs, as the alternate definitions and links to graph theory can be valuable!

*The Handbook of Combinatorial Designs* by Colbourn (2007), as well as Stinson's textbook *Combinatorial Designs: Constructions and Analysis* (2004) served as key references in the development of this formalisation. Additionally, I utilised my notes from the undergraduate design theory courses I took at the University of Queensland in 2016/2017, taught by Dr Herke and Prof. Bryant. 

## How to use this? 

### Requirements

First install Isabelle and set up the Isabelle AFP locally. Then clone the repository to your working folder, and open in Isabelle.

This library depends directly on the following AFP entries: 
- Card_Partitions
- Graph_Theory

The initial section of work (what is in the repository as of May 2021), will be published to the AFP, at which point it is recommended that you use it as you would any other AFP project!

### Isabelle
Some familiarity with Isabelle is recommended for working with this repository. In particular, this library explores a modular approach to formalising design theory and as such heavily relies on Isabelle's Locale system (a tutorial on locales is available within the main Isabelle documentation).

### Suggestions
Feel free to reach out if you have any suggestions/feedback!