
 SHOWLOG (v1.2b)    Lance Ewing (be@ihug.co.nz)
 ===============

  Here it is, the first decent LOGIC viewer available. There may still be
 a few problems with it, so I'd appreciate it if you could notify me of
 any that you encounter so that I can quickly fix them. 

  Peter Kelly has a program called AGIHack on his site that uses SHOWLOG to
 view LOGIC resources. This makes SHOWLOG easier to use.

  A few improvements have been made since version 1.1b. They are as follows:

  - Empty OBJECT files such as the one with Mixed Up Mother Goose is now
    supported.
  - Found a new situation in which an else statement should be a goto and
    have implemented this.
  - A previous problem with the goto statement has been corrected.
  - New option to display variable usage for the logic script.
  - New option to add the message list to the end of the script using the
    format described in the AGI syntax and supported by AGIC and AGIStudio.
    (Presumably MATS will follow soon).

  An error in the way messages were printed for the #message directive list
has been corrected since version 1.2a. 

 With the release of AGI compilers, people are now using SHOWLOG output as
input to these AGI compilers. This has meant that I have had to make a few
changes to the way things are done so that everything is compatible. This
includes the #message directive list that is added to the end of the output
when the -m output is selected.

 There are a number of other changes that may result from discussions being
held at present. 


 Here is a description of the command line options for SHOWLOG:


  showlog [options] logicfile

  -3      Decode a version 3 LOGIC file rather than the default of version 2.
          The difference between the two is that the text in the version 2
          scripts is encrypted with the string "Avis Durgan".

  -s      Stop and wait for a key press after every ten lines of output.
          This should only be used when you are not viewing the output with
          browse.

  -h      Use half height characters (8x8) instead of normal height (8x16).
          This option changes the text screen to 50 lines if your computer
          has VGA.

  -b      Display the output using the BROWSE utility. I've embedded the
          browse utility in SHOWLOG, so you won't have to find it yourself.

  -r      Display the raw LOGIC codes after each line. This option is useful
          for learning the LOGIC format. Use it in conjunction with the LOGIC
          documentation.

  -v      Tag a comment containing the variable usage to the end of the output
          script. This isn't a feature you will use much but I like to be
          able to quickly see how scripts make use of the variable table.

  -m      Add a list of #message directives to the end of the output script
          so that messages can be assigned their respective numbers when the
          scripts are recompiled.


 USEFUL OPTION COMBINATIONS

 1) Example: showlog -b -h logic.2
    This combination will be the most frequently used. It displays the output
    in BROWSE, and the display will be in 50 lines. 

 2) Example: showlog logic.2 > LOGIC002
    This example will produce straight text output and redirect it to the
    file given. 

 3) Example: showlog -h -s logic.2
    This combination is another viewing option where the output produced 
    stops after every ten lines. It also uses the 50 line mode. 

 4) Example: showlog -3 logic.0
    Whenever this options is used, the program assumes that the given file is
    a version 3 LOGIC file. If you get it wrong, then the text messages will
    be a mess.

 5) Example: showlog -r -b -h logic.0
    Use this combination to see how the LOGIC code represents the text
    equivalent. Great for debugging or learning how the codes work.

