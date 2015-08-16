
INCLUDEPATH = src


main: mutualEx2.ml german.ml g2k.ml flash_nodata_3.ml flash_nodata.ml flash_data.ml
	corebuild mutualEx2.byte -I ${INCLUDEPATH} -pkg re2
	corebuild german.byte -I ${INCLUDEPATH} -pkg re2
	corebuild g2k.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_nodata_3.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_nodata.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_data.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_nodata_global_3.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_nodata_global.byte -I ${INCLUDEPATH} -pkg re2

clean:
	rm -rf _build
	rm *.byte
