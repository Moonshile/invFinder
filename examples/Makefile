
INCLUDEPATH = src


main: mutualEx2.ml german.ml g2k.ml flash_nodata_3.ml flash_nodata.ml flash_data.ml
	corebuild mutualEx2.byte -I ${INCLUDEPATH}
	corebuild german.byte -I ${INCLUDEPATH}
	corebuild g2k.byte -I ${INCLUDEPATH}
	corebuild flash_nodata_3.byte -I ${INCLUDEPATH}
	corebuild flash_nodata.byte -I ${INCLUDEPATH}
	corebuild flash_data.byte -I ${INCLUDEPATH}

clean:
	rm -rf _build
	rm *.byte
