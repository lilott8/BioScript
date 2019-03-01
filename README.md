# BioScript

A simple type-safe Domain Specific Language (DSL) for chemistry and biology.



## Usage
usage: main.py
``` 
[-h] [-epa EPA_DEFS] [-abs ABS_INT] -i INPUT [-llvm]
[-s | -dis | -m | -b] [-d]
[-t {inkwell,puddle,m,mfsim,p,i,l,llvm}] [-p PATH]
[-sim {False,True}] [-id {0,1,2,32,4,8,16}] [-nf]
[-smarts SMARTS] [-l {error,warn,none}]
[-tc {disable,naive,n,u,d,union}] [--dbname DBNAME]
[--dbuser DBUSER] [--dbpass DBPASS] [--dbaddr DBADDR]
[--dbdriver {mysql,odbc}]
```
optional arguments:
  -h, --help            show this help message and exit
  
  -s, --store           Is this a storage problem?
  
  -dis, --disposal      Is this a disposal problem?
  -m, --mix             Is this a mixing problem?
  -b, --bioscript       Compile a BioScript program.
  -d, --debug           Enable debug mode.
  -t {inkwell,puddle,m,mfsim,p,i,l,llvm}, --target {inkwell,puddle,m,mfsim,p,i,l,llvm}
                        Platforms to target.
  -p PATH, --path PATH  Working path.

required:
  Required flags for operations.

  -epa EPA_DEFS, --epa-defs EPA_DEFS
                        Location of EPA definition file.
  -abs ABS_INT, --abs-int ABS_INT
                        Location for the abstract interaction files.
  -i INPUT, --input INPUT
                        input file.
  -llvm, --llvm         Use the LLVM for various optimizations.

chemistry:
  Chemistry specific arguments

  -sim {False,True}, --simulate {False,True}
                        Simulate chemistry.
  -id {0,1,2,32,4,8,16}, --identify {0,1,2,32,4,8,16}
                        Chemical identification level.
  -nf, --no-filters     Disable smart filter creation.
  -smarts SMARTS, --smarts SMARTS
                        Length of smart filters to use.

typing:
  Typing specific arguments

  -l {error,warn,none}, --level {error,warn,none}
                        What level to report errors.
  -tc {disable,naive,n,u,d,union}, --typecheck {disable,naive,n,u,d,union}
                        What level to type check this problem.

db:
  Database specific arguments:

  --dbname DBNAME       Name of database.
  --dbuser DBUSER       Database user.
  --dbpass DBPASS       Database password for user.
  --dbaddr DBADDR       Address of database. [IP address | host name]
  --dbdriver {mysql,odbc}
                        Database driver.
                        
### Example Usages:

Enable debug (-d), compile a file (-i ...), disable typechecking (-tc d), declare a working path (-p ...), and target inkwell (-t ...):

```-d -i resources/programs/scratch_pad.bs -tc d -p ./resources/ -t inkwell```