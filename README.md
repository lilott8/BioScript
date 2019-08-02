# BioScript

A simple type-safe Domain Specific Language (DSL) for chemistry and biology.

## Usage
usage: 
``` 
main.py
    [-h] -i INPUT [-d] [-wd WORKING_DIRECTORY] [-o OUTPUT]
    [-t {p,i,l,m,mfsim,llvm,puddle,inkwell}] [-cfg] [-inline]
    [-stats] [-sim {False,True}] [-id {0,1,2,32,4,8,16}] [-nf]
    [-smarts SMARTS] [-tcl {none,error,warn}] [-tc]
    [-tcu {complex,c,simple,s}] [-epa EPA_DEFS] [-abs ABS_INT]
    [--dbname DBNAME] [--dbuser DBUSER] [--dbpass DBPASS]
    [--dbaddr DBADDR] [--dbdriver {odbc,mysql}] [-lib LIBRARY]
    [-flow {p,a,passive,active}] [--cdb CDB]
```
### Optional Arguments:

| Short             | Long                  | Flag                                  | Purpose                                               |
| ------------------|-----------------------|---------------------------------------|-------------------------------------------------------|
| -h                | --help                |                                       | show this help message and exit                       |
| -i                | --input               | path/to/input.bs                      | Location of input file                                |
| -d                | --debug               |                                       | Enable debugging.                                     |
| -t                | --target              | {i,inkwell,p,puddle,m,mfsim,l,llvm}   | What platform do you wish to target?                  |
| -o                | --output              | path/to/output/dir                    | Enable writing output. Must be set to write anything  |
| -wd               | --working-directory   | path/to/directory                     | Directory from where you wish to work                 |
| -cfg              | --write-cfg           |                                       | Write the CFG to a dot file                           |
| -inline           | --inline              |                                       | Inline all non-recursive functions                    |
| -stats            | --stats               |                                       | Print the stats to std out                            |

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
                        
### Setup

You'll need Python3 `(apt-get install python3)`, and GraphViz installed `(apt-get install graphviz)`

If on macOS, install brew, then `brew install python3` and `brew install graphviz`.

BioScript's [grammar](https://github.com/lilott8/BioScriptGrammar "BioScript's Grammar") is attached as a submodule.  Hence, if cloning this repo, make sure to include the `--recursive` tag:

`git clone --recursive https://github.com/lilott8/BioScript`

Also, if [BioScriptGrammar](https://github.com/tlove004/BioScriptGrammar "BioScript's Grammar") is updated (or any other submodule), you'll need to run `git submodule foreach git pull origin master` if your version of git does not do this automatically for you.

Install required python modules: ```pip install -r requirements.txt```

Try running the example usage (below).  It's possible that a C-style comment `/* ... */` is present in some of the grammar files generated by Antlr.  Open any offending files and use proper pythong comments `#` to mitigate this issue.

Some modules may have not installed properly even using the recursive pip install method above.

Continue trying the example usage (below), and `pip install` any missing modules.

Note: you may need to use `pip3 install` if python3/pip3 is not your default python/pip alias.

### Example Usages:

Enable debug (-d), compile a file (-i ...), target inkwell (-t ...), and place the output files in the specified location:

```python main.py -d -i resources/programs/mix.bs -t inkwell -o ./output```

Your output should be a `dag.dot` file and a `json.dag` file.  

You can either use graphviz to create a .png of the generated dag (`dot -Tpng dag.dot -o dag.png`), or use http://www.webgraphviz.com and paste the contents of the .dot or .dag file for visualization.
