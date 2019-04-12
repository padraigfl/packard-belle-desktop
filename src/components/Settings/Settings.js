import React, { Component } from "react";
import { SettingsContext } from "../../contexts/settings";
import { ProgramContext } from "../../contexts/programs";
import {
  Window as AbstractWindow,
  DetailsSection,
  Checkbox,
  Radio,
  ButtonForm
} from "packard-belle";
import Window from "../tools/Window";

import { buildMenu } from "../ExplorerWindow/ExplorerWindow";

import "./_styles.scss";

class Settings extends Component {
  static contextType = SettingsContext;
  state = {
    selected: null,
    bgImg: this.context.bgImg,
    bgStyle: this.context.bgStyle
  };
  timeout;
  fileReader;

  onSelect = selected => this.setState({ selected });

  exit = () => {
    if (this.state.selected) {
      this.context.onClose(this.state.selected, true);
    }
  };

  moveToTop = () => {
    if (this.state.selected) {
      this.context.moveToTop(this.state.selected);
    }
  };

  tempChange = (func, revertFunc) => {
    func();
    setTimeout(() => {
      if (window.confirm("Please confirm this change looks okay")) {
        return;
      }
      revertFunc();
    }, 500);
  };

  updateBackground = () => {
    this.context.updateLocalStorage("bgImg", this.state.bgImg);
  };

  updateBackgroundStyle = e => {
    const val = e.target.value;
    this.context.updateLocalStorage("bgStyle", val);
  };

  removeBackground = () => {
    this.context.removeLocalStorage(["bgImg", "bgStyle"]);
    this.setState({ bgImg: null, bgStyle: null });
  };

  handleFileRead = () => {
    const content = this.fileReader.result;
    if (content.length < 120000) {
      this.setState({ bgImg: content });
    } else {
      window.alert("100kb or less please, sorry =/");
    }
  };

  handleFileChosen = ({ target: { files } }) => {
    this.fileReader = new FileReader();
    this.fileReader.onloadend = this.handleFileRead;
    this.fileReader.readAsDataURL(files[0]);
  };

  render() {
    const { context, props } = this;
    return (
      <ProgramContext.Consumer>
        {program =>
          program.settingsDisplay && (
            <Window
              {...props}
              initialX={200}
              initialY={100}
              initialWidth={280}
              initialHeight={320}
              Component={AbstractWindow}
              title="Control Panel"
              className="Settings"
              onHelp={() => {}} // @todo
              onClose={() => program.toggleSettings(false)}
              menuOptions={buildMenu({
                ...props,
                onClose: program.toggleSettings
              })}
              resizable={false}
              onMinimize={null}
              onMaximize={null}
            >
              <DetailsSection>
                Best avoid all these other than CRT on mobile
              </DetailsSection>
              <DetailsSection title="Customise">
                <Checkbox
                  id="Mobile Portrait View"
                  label="Mobile Portrait View"
                  onChange={context.toggleMobile}
                  checked={context.isMobile === true}
                />
                <Checkbox
                  id="CRT Effect"
                  label="CRT Effect"
                  onChange={context.toggleCrt}
                  checked={context.crt === true}
                />
                <Checkbox
                  id="Fullscreen"
                  label="Fullscreen"
                  onChange={context.toggleFullScreen}
                  checked={context.fullScreen === true}
                />
              </DetailsSection>
              {!context.isMobile && (
                <DetailsSection title="Scale Options (Confirmation Prompt)">
                  <div className="options-row">
                    {[1, 1.5, 2].map(scale => (
                      <Radio
                        id={scale}
                        label={`${scale * 100}%`}
                        value={scale}
                        onChange={e => {
                          this.tempChange(
                            () => context.changeScale(+e.target.value),
                            () => context.changeScale(context.scale)
                          );
                        }}
                        checked={context.scale === scale}
                        isDisabled={context.fullScreen}
                      />
                    ))}
                  </div>
                </DetailsSection>
              )}
              <DetailsSection title="Background">
                {this.context.bgImg ? (
                  <>
                    <div>
                      {["tile", "stretch", "contain"].map(v => (
                        <Radio
                          key={v}
                          id={v}
                          label={v}
                          value={v}
                          onChange={this.updateBackgroundStyle}
                          checked={this.context.bgStyle === v}
                        />
                      ))}
                    </div>
                    <ButtonForm onClick={this.removeBackground}>
                      Reset Background
                    </ButtonForm>
                  </>
                ) : (
                  <div>
                    <input
                      type="file"
                      onChange={this.handleFileChosen}
                      name="bgImg"
                      id="bgImg"
                    />
                    <div>
                      <ButtonForm
                        onClick={this.updateBackground}
                        isDisabled={!this.state.bgImg}
                      >
                        Upload Image
                      </ButtonForm>
                    </div>
                  </div>
                )}
              </DetailsSection>
              {this.state.tempChange && "Previewing Changes"}
            </Window>
          )
        }
      </ProgramContext.Consumer>
    );
  }
}

export default Settings;
