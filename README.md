# BioScript

A simple type-safe Domain Specific Language (DSL) for chemistry and biology.



## Usage
usage: 
``` 
 main.py 
    [-h] -i INPUT [-d] [-t {p,mfsim,llvm,l,i,inkwell,m,puddle}]
    [-wd WORKING_DIRECTORY]
    [-p {compile,d,disposal,b,c,bioscript,mix,s,store,m}]
    [-sim {False,True}] [-id {0,1,2,32,4,8,16}] [-nf]
    [-smarts SMARTS] [-tcl {warn,none,error}]
    [-tc {u,union,naive,disable,d,n}] [-epa EPA_DEFS]
    [-abs ABS_INT] [--dbname DBNAME] [--dbuser DBUSER]
    [--dbpass DBPASS] [--dbaddr DBADDR] [--dbdriver {mysql,odbc}]
```
### Optional Arguments:

| Short             | Long                  | Flag                  | Purpose                                               |
| ------------------|-----------------------|-----------------------|-------------------------------------------------------|
| -h                | --help                |                       | show this help message and exit                       |
| -i                | --input               | path/to/input.bs      | Location of input file                                |
| -d                | --debug               |                       | Enable debugging.                                     |
| -t                | --target              | {inkwell,puddle,m,mfsim,p,i,l,llvm} | What platform do you wish to target?    |
| -wd               | --working-directory   | path/to/directory     | Directory from where you wish to work                 |
| -p                | --problem             | {b, bioscript, c, compile, m, mix, s, store} | What problem are you solving?  |
|

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
| -tc               | --typecheck           | {disable,naive,n,u,d,union}   | How to typecheck default is `naive`                                                           |
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

Enable debug (-d), compile a file (-i ...), disable typechecking (-tc d), declare a working path (-p ...), and target inkwell (-t ...):

```-d -i resources/programs/scratch_pad.bs -tc d -p ./resources/ -t inkwell```