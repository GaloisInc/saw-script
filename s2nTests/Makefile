.PHONY: all saw-script s2n hmac drbg sike bike tls hmac-failure awslc blst

all: hmac drbg sike bike tls hmac-failure awslc blst
saw-script:
	docker-compose build saw-script
	docker-compose run saw-script
s2n:
	docker-compose build s2n
hmac: s2n
	docker-compose run -v ./s2n-hmac.cache:/s2n.cache s2n sawHMAC
drbg: s2n
	docker-compose run -v ./s2n-drbg.cache:/s2n.cache s2n sawDRBG
sike: s2n
	docker-compose run -v ./s2n-sike.cache:/s2n.cache s2n sawSIKE
bike: s2n
	docker-compose run -v ./s2n-bike.cache:/s2n.cache s2n sawBIKE openssl-1.0.2
tls: s2n
	docker-compose run -v ./s2n-tls.cache:/s2n.cache s2n tls
hmac-failure: s2n
	docker-compose run -v ./s2n-hmac-failure.cache:/s2n.cache s2n sawHMACFailure

awslc-container:
	docker-compose build awslc
awslc: awslc-container
	docker-compose run -v ./s2n-awslc.cache:/awslc.cache awslc

blst-container:
	docker-compose build blst
blst: blst-container
	docker-compose run -v ./s2n-blst.cache:/blst.cache blst
