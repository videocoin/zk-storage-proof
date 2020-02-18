package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"os/exec"
	"os/user"

	"github.com/videocoin/zk-storage-proof/go-apps/sla"
)

func main() {
	usr, _ := user.Current()
	workFolder := flag.String("work", usr.HomeDir+"/test/", "folder containing intermediate files")
	input := flag.String("input", "", "input file")
	output := flag.String("output", "", "output file")
	flag.Parse()

	if *input == "" || *output == "" {
		flag.PrintDefaults()
		os.Exit(1)
	}

	//
	// Extract frames
	//
	cmd := exec.Command("extract-frame", "-f", "0", "-c", "300", "--scale", "--input", *input, "--output", *workFolder+"scaled-frames.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err := cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("extracting frames")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()
	//
	// generate phashes
	//
	cmd = exec.Command("rust-phash", *workFolder+"scaled-frames.txt", *workFolder+"phashes.txt")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating phashes")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	var b1 bytes.Buffer
	var b2 bytes.Buffer
	//
	// generate challenge
	//
	cmd = exec.Command("zkptrans", "zkporchallenge", *workFolder+"phashes.txt")
	cmd.Stdout = &b1
	cmd.Stderr = &b2
	fmt.Println("generating challenge")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	// Create request
	sla := sla.SlaStorage{
		Url:          *output,
		ProofType:    sla.ProofPhashMerkleZksnark,
		PublicInputs: b1.String(),
	}
	sla_json, err := json.Marshal(sla)

	hasher := sha256.New()
	hasher.Write(sla_json)
	sla_id := base64.URLEncoding.EncodeToString(hasher.Sum(nil))
	reward := "1vid"
	cmd = exec.Command("vccli", "tx", "sla", "createSla", reward, sla_id, string(sla_json), "--yes", "--from", "tester0")
	//stdout, err := cmd.StdoutPipe()
	stderr, err = cmd.StderrPipe()
	if err != nil {
		log.Fatal(err)
	}
	fmt.Println("generating transaction")
	err = cmd.Start()
	print(stderr)

	cmd.Wait()

	fmt.Println("Finished:", err)
}

func print(console io.ReadCloser) {
	scanner := bufio.NewScanner(console)
	scanner.Split(bufio.ScanWords)
	for scanner.Scan() {
		m := scanner.Text()
		fmt.Print(m + " ")
	}
}
