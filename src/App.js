import React, { Component } from "react";
import { Theme, ExplorerView, TaskBar, ExplorerIcon } from "packard-belle";
import logo from "./logo.svg";
import "./App.css";
import Explorer from "./components/ExplorerWindow";

const testOptions = [
  {
    title: "Test",
    icon: logo,
    onClick: () => {},
    options: [
      {
        title: "Test",
        icon: logo,
        onClick: () => {}
      }
    ]
  },
  {
    title: "Test2",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test3",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test4",
    icon: logo,
    onClick: () => {}
  }
];

class App extends Component {
  state = {
    width: 300,
    height: 300
  };

  onResize = (event, { element, size }) => {
    this.setState({ width: size.width, height: size.height });
  };

  render() {
    return (
      <Theme className="desktop">
        <ExplorerView options={testOptions}>
          {testOptions.map(option => (
            <ExplorerIcon key={option.title} {...option} />
          ))}
        </ExplorerView>
        <TaskBar options={testOptions} />
        <Explorer scale={2} />
      </Theme>
    );
  }
}

// include corner thing if resizable
// body of explorer window needs to fill space

export default App;
