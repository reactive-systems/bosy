#! /usr/bin/env bash

#find installed docker command

DOCKER_COMMAND=podman


function get_abs_filename() {
 	# $1 : relative filename
  	echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
}

command=$1
command=${command,,}


if [ $command == "build" ]; then

	if [ $(tr $2) == "full" ]; then
		$DOCKER_COMMAND build -t localhost/bosyrunner:full full
		exit $?
	fi
	$DOCKER_COMMAND  build -t localhost/bosyrunner:default default
exit $?
fi

#first param is run/ build, second is build type,
# third is path, everything after that is bosy params
if [ $command == "run" ]; then
	bosy_type=$2
	mount_path=$3

	if [ -f $mount_path ]; then
		absfn=$(get_abs_filename $mount_path)
		mount=$(dirname "$absfn")
		file=$(basename "$absfn")
		$DOCKER_COMMAND run -v $mount:/root/files:Z "localhost/bosyrunner:$bosy_type" /root/files/$file ${@:4}
		exit $?
	fi

	$DOCKER_COMMAND run -v $mount_path:/root/files:Z localhost/bosyrunner:$bosy_type ${@:4}

exit $?
fi
