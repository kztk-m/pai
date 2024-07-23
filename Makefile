HSOPTSC    = #-fllvm -optlo-O3 #-fvia-C -optc -w # -optc -frename-registers # -optc -O3 #-optc -march=core2 
HSOPTS     = -O2 -rtsopts
HSOPTS_ARC = 
HSOPTS_EXP = $(HSOPTS) $(HSOPTSC) # -ddump-simpl-stats 

TOP = .
EXECUTABLE = $(TOP)/PaI
EXAMPLE_DIR = $(TOP)/examples
EXAMPLE_SUFFIX = txt
EXAMPLES = $(shell ls $(EXAMPLE_DIR)/*.$(EXAMPLE_SUFFIX))


EXP_SRC    = Experiment.hs
EXP_TARGET = Experiment

HSSRC = $(shell find ./ -name "*.hs")

.PHONY : doc clean example distclean time experiment experiment_opt prof


all : $(EXECUTABLE) 


$(EXECUTABLE) : 
	cabal build -j 
	cabal install --installdir=$(TOP) --install-method=copy --overwrite-policy=always
	# if [ -d ./dist-newstyle/ ]; then \
	# 	cp `find ./dist-newstyle -name 'PaI' -type f` ./$(EXECUTABLE); \
	# elif [ -d ./dist/ ]; then \
	# 	cp ./dist/build/PaI/PaI ./$(EXECUTABLE); \
	# else \
	# 	echo "Error: failed to find executable to copy"; \
	# fi 



example : $(EXECUTABLE)
	for f in $(EXAMPLES); \
	do \
	   echo $$f; \
	   fn=$${f##*/}; \
	   mn=`echo $${fn%\.*} | tr "[a-z]" "[A-Z]"`; \
	   hs="$${mn}.hs"; \
	   gta="$${mn}.gta"; \
	   $(EXECUTABLE) -t -d $${f%\.*}.$(EXAMPLE_SUFFIX) -m $${mn} -i MyData > $(EXAMPLE_DIR)/$${hs} 2> $(EXAMPLE_DIR)/$${gta} ; \
	   tail -1 $(EXAMPLE_DIR)/$${gta}; \
	done

experiment_recomp: HSOPTS_EXP += -fforce-recomp 
experiment_recomp: experiment 

experiment : 
	ghc -i$(EXAMPLE_DIR)  $(HSOPTS_EXP) --make $(EXP_SRC) -o $(EXP_TARGET)


time : $(EXECUTABLE)
	for f in $(EXAMPLES); \
	do \
		echo $${f%\.*}; \
		time $(EXECUTABLE) $${f%\.*}.$(EXAMPLE_SUFFIX) > /dev/null;  \
		echo "\n\n"; \
	done

clean :
	rm -f *.hi *.o
	rm -f */*.hi */*.o 
	rm -f $(EXAMPLE_DIR)/*.hs
	rm -f $(EXAMPLE_DIR)/*.gta
	cabal clean 
	rm -f $(EXECUTABLE)
	rm -f $(EXECUTABLE).exe
	rm -f $(EXP_TARGET)
	rm -f $(EXP_TARGET).exe
	rm -f *~
	rm -f */*~

distclean: clean

#dist: clean
#	cd ../; tar czvf PaI.tar.gz --exclude 'CVS' --exclude '.cvsignore' PaI/
#	mv ../PaI.tar.gz PaI.tar.gz
#	cp PaI.tar.gz PaI`date +'%Y%m%d'`.tar.gz

doc: example
	make -C doc
