#!/bin/bash
sudo docker stop coq
sudo docker start -i coq
success=$?

if [ $success -eq 1 ]
then
	sudo docker run --name="coq" -t -v "${PWD}/../../coq":/home/coq -i dom/coq:v1 
fi

