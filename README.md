# BioScript

A simple type-safe Domain Specific Language (DSL) for chemistry and biology.

## Usage
usage: 
``` 
main.py [-h] -i INPUT [-d] [-wd WORKING_DIRECTORY] [-o OUTPUT]
       [-t {m,i,p,inkwell,l,llvm,ir,mfsim,puddle}] [-cfg] [-inline]
       [-stats] [-lu] [-sim {False,True}] [-id {0,1,2,32,4,8,16}]
       [-nf] [-smarts SMARTS] [-tcl {none,warn,error}] [-tc]
       [-tcu {complex,simple,s,c}] [-epa EPA_DEFS] [-abs ABS_INT]
       [--dbname DBNAME] [--dbuser DBUSER] [--dbpass DBPASS]
       [--dbaddr DBADDR] [--dbdriver {odbc,mysql}] [-lib LIBRARY]
       [-flow {passive,p,a,active}] [--cdb CDB] [--schema SCHEMA]
       [--validate]
```
### Optional Arguments:

| Short             | Long                  | Flag                                      | Purpose                                               |
| ------------------|-----------------------|-------------------------------------------|-------------------------------------------------------|
| -h                | --help                |                                           | show this help message and exit                       |
| -i                | --input               | path/to/input.bs                          | Location of input file                                |
| -d                | --debug               |                                           | Enable debugging.                                     |
| -t                | --target              | {i,inkwell,p,puddle,m,mfsim,l,llvm, ir,}  | What platform do you wish to target?                  |
| -o                | --output              | path/to/output/dir                        | Enable writing output. Must be set to write anything  |
| -wd               | --working-directory   | path/to/directory                         | Directory from where you wish to work                 |
| -cfg              | --write-cfg           |                                           | Write the CFG to a dot file                           |
| -inline           | --inline              |                                           | Inline all non-recursive functions                    |
| -lu               | --loopunroll          |                                           | Unroll all un-rollable loops                          |
| -stats            | --stats               |                                           | Print the stats to std out                            |
| -cfg              | --write-cfg           |                                           | Write the programs control flow graph to disk         |


### Chemistry:
**Chemistry specific arguments**

| Short             | Long                  | Flag                  | Purpose                           |
| ------------------|-----------------------|-----------------------|-----------------------------------|
| -sim              | --simulate            | {True, False}         | Simulate chemistry?               |
| -id               | --identify            | {0,1,2,32,4,8,16}     | Chemical identification level     |
| -nf               | --no-filters          |                       | Disable smart filter creation     |
| -smarts           | --smarts              | 0-255                 | Length of smarts file to use      |

### Typing:
**Typing specific arguments**

| Short             | Long                  |  Flag                         | Purpose                                                                                       |
| ------------------|-----------------------|-------------------------------|-----------------------------------------------------------------------------------------------|
| -tcl              | --typechecklevel      | {error, warn, none}           | What interactions elicit notifications                                                        |
| -tc               | --typecheck           |                               | Enable type checking of input program                                                         |
| -tcu              | --typesused           | {s, simple, c, complex}       | What types to use to typecheck a program, s = {mat, nat, real}, c = {all types in chemtype}   |
| -epa              | --epa-defs            | Path/to/epa_defs.json         | Location of the EPA definition file (default: `./resources/epa.json`)                         |
| -abs              | --abs-int             | path/to/abs-int.txt           | Location of the abstract interaction file (default: `./resources/abstract-interaction.txt`)   |

### DB:
**Database specific arguments**

| Flag              | Argument      | Purpose                                   |
|-------------------|---------------|-------------------------------------------|
| --dbname          | str           | Name of database.                         |
| --dbuser          | str           | Database user.                            |
| --dbpass          | str           | Database password for user.               |
| --dbaddr          | {IP, Host}    | Address of database.                      |
| --dbdriver        | {mysql,odbc}  | Database driver.                          |

### Inkwell:
**Inkwell specific (`-t inkwell`) flags**

| Short             | Long                  | Flag                              | Purpose                                               |
| ------------------|-----------------------|-----------------------------------|-------------------------------------------------------|
| -lib              | --library             | path/to/json/component/lib        | The path to the component library                     |
| -flow             | --flow                | {p, a, passive, active}           | Which type of flow-based device are you targeting     |
| -cdb              |                       | database                          | Name of component database (not supported)            |
|                   | --schema              | Path to schema.json               | The `ParchMint` schema file                           |
|                   | --validate            |                                   | Validate a netlist against the `ParchMint` schema     |
                        
### Setup

You'll need Python3 `(apt-get install python3)`, and GraphViz installed `(apt-get install graphviz)`

If on macOS, install brew, then `brew install python3` and `brew install graphviz`.

BioScript's [grammar](https://github.com/lilott8/BioScriptGrammar "BioScript's Grammar") is attached as a submodule.  Hence, if cloning this repo, make sure to include the `--recursive` tag:

`git clone --recursive https://github.com/lilott8/BioScript`

Also, if [BioScriptGrammar](https://github.com/lilott8/BioScriptGrammar "BioScript's Grammar") (or any other submodule) is updated, you'll need to run `git submodule foreach git pull origin master` if your version of git does not do this automatically for you.

Install required python modules: ```pip install -r requirements.txt```

Try running the example usage (below).  It's possible that a C-style comment `/* ... */` is present in some of the grammar files generated by Antlr.  Open any offending files and use proper pythong comments `#` to mitigate this issue.

Some modules may have not installed properly even using the recursive pip install method above.

Continue trying the example usage (below), and `pip install` any missing modules.

Note: you may need to use `pip3 install` if python3/pip3 is not your default python/pip alias.

### Example Usages:

Enable debug (-d), compile a file (-i ...), target `BioScript's` IR (-t ...), and place the output files in the specified location:

```python main.py -d -i tests/test_cases/mix/ir_sisd.bs -t ir -o ./output -cfg```

Your output folder should includ the following files: `ir_sisd_main_dag.dot`, `ir_sisd.ir`, `ir_sisd_main_basic_blocks.dot`.  

You can either use graphviz to create a .png of the generated dag (`dot -Tpng dag.dot -o dag.png`), or use http://www.webgraphviz.com and paste the contents of the .dot or .dag file for visualization.
