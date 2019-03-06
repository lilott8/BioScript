# BioScript

A simple type-safe Domain Specific Language (DSL) for chemistry and biology.



## Usage
usage: 
``` 
 main.py 
    [-h] -i INPUT [-d] [-t {inkwell,p,puddle,llvm,mfsim,l,m,i}]
    [-wd WORKING_DIRECTORY] [-sim {False,True}]
    [-id {0,1,2,32,4,8,16}] [-nf] [-smarts SMARTS]
    [-tcl {error,warn,none}] [-tc] [-tcu {simple,c,complex,s}]
    [-epa EPA_DEFS] [-abs ABS_INT] [--dbname DBNAME]
    [--dbuser DBUSER] [--dbpass DBPASS] [--dbaddr DBADDR]
    [--dbdriver {mysql,odbc}]

```
### Optional Arguments:

| Short             | Long                  | Flag                                  | Purpose                                               |
| ------------------|-----------------------|---------------------------------------|-------------------------------------------------------|
| -h                | --help                |                                       | show this help message and exit                       |
| -i                | --input               | path/to/input.bs                      | Location of input file                                |
| -d                | --debug               |                                       | Enable debugging.                                     |
| -t                | --target              | {i,inkwell,p,puddle,m,mfsim,l,llvm}   | What platform do you wish to target?                  |
| -wd               | --working-directory   | path/to/directory                     | Directory from where you wish to work                 |

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
                        
### Example Usages:

Enable debug (-d), compile a file (-i ...), and target inkwell (-t ...):

```-d -i resources/programs/scratch_pad.bs -tc d -p ./resources/ -t inkwell```