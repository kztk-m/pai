all:
	pandoc -f markdown -t html --email-obfuscation=references -H header.txt index.txt -o index.html
	if test -e examples; then true;else mkdir examples; fi
	cp ../examples/*.txt examples/
	cp ../examples/*.hs  examples/
	cp ../examples/*.gta examples/
	cp ../InvUtil.hs     .
	cp ../MyData.hs      .

clean:
	rm -f index.html
	rm -rf ./examples
	rm ./*.hs