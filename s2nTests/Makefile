.PHONY: all saw-script s2n hmac drbg sike bike tls hmac-failure

all: hmac drbg sike bike tls hmac-failure
saw-script:
	docker-compose build saw-script
	docker-compose run saw-script
s2n:
	docker-compose build s2n
hmac: s2n
	docker-compose run s2n sawHMAC
drbg: s2n
	docker-compose run s2n sawDRBG
sike: s2n
	docker-compose run s2n sawSIKE
bike: s2n
	docker-compose run s2n sawBIKE openssl-1.0.2
tls: s2n
	docker-compose run s2n tls
hmac-failure: s2n
	docker-compose run s2n sawHMACFailure
